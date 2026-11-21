import Langlands.Analysis.L2BochnerRepresentative
import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Pointwise representatives of compactly weighted quotient orbits -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i

section Pointwise

variable {Y : Type v} [TopologicalSpace Y]

private theorem continuous_weightedQuotientOrbit (b : C(Y, AdelicGroupPoints F G))
    (w : C(Y, ℂ)) (h : C(Q, ℂ)) :
    Continuous (fun yq : Y × Q => w yq.1 * h (LeftCosetSpace.rightTranslate Γ (b yq.1) yq.2)) :=
  (w.continuous.comp continuous_fst).mul (h.continuous.comp
    (continuous_smul.comp
      ((MulOpposite.continuous_op.comp (b.continuous.comp continuous_fst)).prodMk continuous_snd)))

variable [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- Integrate a continuous representative against a compactly supported weight, with the
translations allowed to be parametrized by a continuous map into the adelic group. -/
def weightedQuotientOrbitIntegral (b : C(Y, AdelicGroupPoints F G))
    (w : C(Y, ℂ)) (hw : HasCompactSupport w) (h : C(Q, ℂ)) : C(Q, ℂ) where
  toFun q := ∫ y, w y * h (LeftCosetSpace.rightTranslate Γ (b y) q) ∂ν
  continuous_toFun := by
    apply continuousOn_univ.mp
    refine continuousOn_integral_of_compact_support hw ?_ ?_
    · exact ((continuous_weightedQuotientOrbit F G T i b w h).comp continuous_swap).continuousOn
    · intro q y _ hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

@[simp]
theorem weightedQuotientOrbitIntegral_apply (b : C(Y, AdelicGroupPoints F G))
    (w : C(Y, ℂ)) (hw : HasCompactSupport w) (h : C(Q, ℂ)) (q : Q) :
    weightedQuotientOrbitIntegral F G T i ν b w hw h q =
      ∫ y, w y * h (LeftCosetSpace.rightTranslate Γ (b y) q) ∂ν := rfl

end Pointwise

section L2

variable [LocallyOfFiniteType G.X.hom]
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
  {Y : Type v} [TopologicalSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR

/-- Integrating a continuous compactly weighted orbit in the canonical quotient `L²`
space gives the class of the corresponding continuous pointwise integral. -/
def GroupSchemeQuotientL2IntegratedRepresentativeStatement
    [SecondCountableTopology Y] [SFinite ν] : Prop :=
  ∀ (b : C(Y, AdelicGroupPoints F G)) (w : C(Y, ℂ)) (hw : HasCompactSupport w)
    (φ : Lp ℂ 2 μQ) (h : C(Q, ℂ)),
    (φ : Q → ℂ) =ᵐ[μQ] h →
    Integrable (fun y => w y • ρ (b y) φ) ν ∧
    ((∫ y, w y • ρ (b y) φ ∂ν : Lp ℂ 2 μQ) : Q → ℂ) =ᵐ[μQ]
      weightedQuotientOrbitIntegral F G T i ν b w hw h

/-- The Bochner integral and the continuous pointwise integral have the same class. -/
theorem groupSchemeQuotientL2IntegratedRepresentative
    [SecondCountableTopology Y] [SFinite ν] :
    GroupSchemeQuotientL2IntegratedRepresentativeStatement F G T i hi I e hc ν := by
  intro b w hw φ h hrep
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  have hwI : Integrable w ν := w.continuous.integrable_of_hasCompactSupport hw
  have hOrb : AEStronglyMeasurable (fun y => ρ (b y) φ) ν :=
    ((haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous.comp
      b.continuous).stronglyMeasurable.aestronglyMeasurable
  have hI : Integrable (fun y => w y • ρ (b y) φ) ν := by
    apply (hwI.norm.mul_const ‖φ‖).mono' (hwI.aestronglyMeasurable.smul hOrb)
    exact Filter.Eventually.of_forall fun y => by
      change ‖w y • haarQuotientL2BoundedRightAction F G T i hi I e hc (b y) φ‖ ≤ _
      rw [norm_smul, norm_haarQuotientL2BoundedRightAction]
  refine ⟨hI, Langlands.Analysis.coeFn_integral_l2_ae_eq
    (f := fun yq => w yq.1 * h (LeftCosetSpace.rightTranslate Γ (b yq.1) yq.2)) hI ?_ ?_⟩
  · exact (continuous_weightedQuotientOrbit F G T i b w h).stronglyMeasurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      filter_upwards [Lp.coeFn_smul (w y) (ρ (b y) φ),
        coeFn_quotientL2RightTranslate F G T i μQ hR (b y) φ,
        (hR (b y)).quasiMeasurePreserving.ae_eq_comp hrep] with q hsmul htranslate hφ
      change (w y • ρ (b y) φ : Lp ℂ 2 μQ) q = _
      rw [hsmul]
      change w y * quotientL2RightTranslate F G T i μQ hR (b y) φ q = _
      rw [htranslate]
      change w y * φ (LeftCosetSpace.rightTranslate Γ (b y) q) = _
      exact congrArg (w y * ·) hφ

end L2

end Langlands.Automorphic.GroupSchemeFunctions
