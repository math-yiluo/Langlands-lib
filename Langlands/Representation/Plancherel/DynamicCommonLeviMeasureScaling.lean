import Langlands.Representation.Plancherel.DynamicCommonLeviComposition
import Langlands.Representation.Plancherel.StandardIntertwiningMeasure
import Langlands.Analysis.Local.QuotientInvariantComparison

/-! # Change of compact Haar normalization for actual common-Levi intertwiners -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open QuotientIntegration

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance radicalMeasurable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (radical ψ) := borel _
local instance radicalBorel (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (radical ψ) := ⟨rfl⟩
local instance intersectionMeasurable (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace ((radical ψ).subgroupOf (radical ψ')) := borel _
local instance intersectionBorel (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace ((radical ψ).subgroupOf (radical ψ')) := ⟨rfl⟩
local instance quotientMeasurable (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (QuotientSpace (U := radical ψ) (radical ψ')) := borel _
local instance quotientBorel (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (QuotientSpace (U := radical ψ) (radical ψ')) := ⟨rfl⟩

variable (K L : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hL : IsCompact (L : Set (RationalPoint F G.X)))
  (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "μK" => radicalHaar ψ' K hK
local notation "μL" => radicalHaar ψ' L hL
local notation "ηK" => pairIntersectionHaar K hK ψ ψ'
local notation "ηL" => pairIntersectionHaar L hL ψ ψ'
local notation "qK" => pairQuotientMeasure K hK ψ ψ'
local notation "qL" => pairQuotientMeasure L hL ψ ψ'
local notation "a" => haarScalarFactor μL μK
local notation "b" => haarScalarFactor ηL ηK

/-- The quotient scale is the ratio of the target-radical and intersection Haar scales. -/
def pairQuotientHaarScale : ℝ≥0 := a / b

theorem pairQuotientHaarScale_pos : 0 < pairQuotientHaarScale K L hK hL ψ ψ' :=
  div_pos (haarScalarFactor_pos_of_isHaarMeasure μL μK)
    (haarScalarFactor_pos_of_isHaarMeasure ηL ηK)

/-- Changing the source compact open scales the actual quotient measure by the exact ratio. -/
theorem pairQuotientMeasure_changeCompact :
    qL = pairQuotientHaarScale K L hK hL ψ ψ' • qK := by
  let H := (radical ψ).subgroupOf (radical ψ')
  have hH : IsClosed (H : Set (radical ψ')) := (radical_isClosed ψ).preimage continuous_subtype_val
  let : LocallyCompactSpace (radical ψ') := (radical_isClosed ψ').locallyCompactSpace
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  have hμ : μL = a • μK := isMulLeftInvariant_eq_smul_of_regular μL μK
  have hη : ηL = b • ηK := isMulLeftInvariant_eq_smul_of_regular ηL ηK
  have hqK := pairQuotientMeasure_isCompatible K hK ψ ψ'
  have hqL := pairQuotientMeasure_isCompatible L hL ψ ψ'
  let : Measure.Regular qK := hqK.regular
  let : Measure.Regular qL := hqL.regular
  obtain ⟨c, hc, hq⟩ := exists_pos_smul_eq_of_rightInvariant_quotient H hH ηK qL qK
    hqL.nonzero hqK.nonzero hqL.right_invariant hqK.right_invariant
  let d : ℝ≥0 := c.toNNReal
  have hd : qL = d • qK := by
    simpa only [d, ENNReal.ofReal, ← ENNReal.smul_def] using hq
  obtain ⟨f, hf⟩ := exists_compact_integral_ne_zero μK (NeZero.ne μK)
  let F₀ : radical ψ' → ℂ := Complex.ofReal ∘ f
  have hcont : Continuous F₀ := Complex.continuous_ofReal.comp f.continuous
  have hsupp : HasCompactSupport F₀ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hf₀ : (∫ x, F₀ x ∂μK) ≠ 0 := by
    rw [show (∫ x, F₀ x ∂μK) = Complex.ofReal (∫ x, f x ∂μK) from integral_ofReal]
    exact_mod_cast hf
  have havg : quotientAverage H ηL F₀ = fun q => b • quotientAverage H ηK F₀ q := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      change (∫ h : H, F₀ (h.val * x) ∂ηL) = b • (∫ h : H, F₀ (h.val * x) ∂ηK)
      calc
        (∫ h : H, F₀ (h.val * x) ∂ηL) = ∫ h : H, F₀ (h.val * x) ∂(b • ηK) :=
          congrArg (fun ν => ∫ h : H, F₀ (h.val * x) ∂ν) hη
        _ = _ := integral_smul_nnreal_measure _ _
  have hI := hqL.integral_formula F₀ hcont hsupp
  change (∫ q, quotientAverage H ηL F₀ q ∂qL) = ∫ x, F₀ x ∂μL at hI
  rw [havg, hd, hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure] at hI
  change d • (∫ q, (b : ℝ) • quotientAverage H ηK F₀ q ∂qK) = a • (∫ x, F₀ x ∂μK) at hI
  rw [integral_smul, hqK.integral_formula F₀ hcont hsupp] at hI
  change d • (b • (∫ x, F₀ x ∂μK)) = a • (∫ x, F₀ x ∂μK) at hI
  rw [smul_smul] at hI
  have hdb : d * b = a := by
    change Complex.ofReal (↑(d * b) : ℝ) * (∫ x, F₀ x ∂μK) =
      Complex.ofReal (a : ℝ) * (∫ x, F₀ x ∂μK) at hI
    exact NNReal.coe_injective (Complex.ofReal_injective (mul_right_cancel₀ hf₀ hI))
  rw [hd, pairQuotientHaarScale, ← (eq_div_iff (haarScalarFactor_pos_of_isHaarMeasure ηL ηK).ne').mpr hdb]

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- The full domain of the actual pair integral is independent of the compact Haar scale. -/
theorem pairFullDomainRegion_changeCompact :
    pairFullDomainRegion χ L hL ψ hψ ψ' A = pairFullDomainRegion χ K hK ψ hψ ψ' A := by
  ext z
  simp only [pairFullDomainRegion, standardIntertwiningFullDomainRegion, Set.mem_ofPred_eq,
    pairQuotientMeasure_changeCompact K L hK hL ψ ψ',
    domain_smul_measure _ _ _ _ _ _ (pairQuotientHaarScale_pos K L hK hL ψ ψ').ne']

/-- The actual pair operators change by the same positive scalar at every full-domain point. -/
theorem pairFamily_changeCompact
    (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (hz : z.val ∈ pairFullDomainRegion χ L hL ψ hψ ψ' A)
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    pairFamily χ L hL ψ hψ ψ' hψ' hδ A ⟨z.val, hz⟩ f =
      (((pairQuotientHaarScale K L hK hL ψ ψ' : ℝ≥0) : ℝ) : ℂ) •
        pairFamily χ K hK ψ hψ ψ' hψ' hδ A z f := by
  let B := A.twist (parameterTransport χ z.val).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val))
  have h₁ := pairFamily_spec χ L hL ψ hψ ψ' hψ' hδ A ⟨z.val, hz⟩ f
  have h₂ := HasIntegral.smul_measure_nnreal (commonDecomposition χ ψ hψ)
    (radical_isClosed ψ) (radical ψ') B qK (pairFamily_spec χ K hK ψ hψ ψ' hψ' hδ A z f)
    (pairQuotientHaarScale K L hK hL ψ ψ')
  rw [pairQuotientMeasure_changeCompact K L hK hL ψ ψ'] at h₁
  have heq (g : RationalPoint F G.X) :=
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique (ρ := B.representation)
      (compactCofinal (levi_isClosed χ)) B.property (h₁ g) (h₂ g)
  exact Subtype.ext (Subtype.ext (funext heq))

end Langlands.Plancherel.DynamicCommonLeviComposition
