import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Global.AdelicParabolicModulus
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Right translation and compact averages on the full rational quotient `L²`

The action used on the target of the adelic spectral transform is pullback along
positive right translation on `G(F) \ G(𝔸)`. We construct it on the actual Haar
quotient, prove joint continuity, and identify the weighted compact averages with
their almost-everywhere pointwise formulas. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "Q" => RationalQuotient F G
local notation "Γ" => rationalSubgroup F G
local notation "μQ" => rationalQuotientHaarMeasure F G
local notation "H" => Lp ℂ 2 μQ

private theorem rightAction_preserving (hG : IsConnectedReductive G) (y : AdelicGroupPoints F G) :
    MeasurePreserving (LeftCosetSpace.rightTranslate Γ y) μQ μQ := by
  let := (adelicHaarUnimodularity.{u}).2 F G hG
  exact measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G y

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem rightAction_out (y : AdelicGroupPoints F G) (x : Q) :
    LeftCosetSpace.rightTranslate Γ y x = LeftCosetSpace.mk Γ (x.out * y) := calc
  LeftCosetSpace.rightTranslate Γ y x = LeftCosetSpace.rightTranslate Γ y
      (LeftCosetSpace.mk Γ x.out) :=
    congrArg (LeftCosetSpace.rightTranslate Γ y) (Quotient.out_eq x).symm
  _ = _ := LeftCosetSpace.rightTranslate_mk Γ y x.out

/-- Positive right translation `R(y) f(x) = f(x y)` on the full rational quotient `L²`,
using the quotient of ambient Haar measure by counting measure. -/
def rationalQuotientL2RightAction (hG : IsConnectedReductive G) :
    AdelicGroupPoints F G →* (H →L[ℂ] H) where
  toFun y := (Lp.compMeasurePreservingₗᵢ ℂ _ (rightAction_preserving hG y)).toContinuousLinearMap
  map_one' := by
    ext f : 1
    change Lp.compMeasurePreserving _ (rightAction_preserving hG 1) f = f
    have he : LeftCosetSpace.rightTranslate Γ (1 : AdelicGroupPoints F G) = id :=
      funext (LeftCosetSpace.rightTranslate_one Γ)
    simp only [he, Lp.compMeasurePreserving_id_apply]
  map_mul' y z := by
    ext f : 1
    change Lp.compMeasurePreserving _ (rightAction_preserving hG (y * z)) f =
      Lp.compMeasurePreserving _ (rightAction_preserving hG y)
        (Lp.compMeasurePreserving _ (rightAction_preserving hG z) f)
    have he : LeftCosetSpace.rightTranslate Γ (y * z) =
        LeftCosetSpace.rightTranslate Γ z ∘ LeftCosetSpace.rightTranslate Γ y :=
      funext fun x => (LeftCosetSpace.rightTranslate_mul Γ y z x).symm
    simp only [he, Lp.compMeasurePreserving_comp_apply f (rightAction_preserving hG z)
      (rightAction_preserving hG y)]

theorem norm_rationalQuotientL2RightAction (hG : IsConnectedReductive G)
    (y : AdelicGroupPoints F G) (f : H) :
    ‖rationalQuotientL2RightAction hG y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (rightAction_preserving hG y)

theorem coeFn_rationalQuotientL2RightAction (hG : IsConnectedReductive G)
    (y : AdelicGroupPoints F G) (f : H) :
    (rationalQuotientL2RightAction hG y f : Q → ℂ) =ᵐ[μQ]
      fun (x : Q) => f (LeftCosetSpace.mk Γ (x.out * y)) := by
  refine (Lp.coeFn_compMeasurePreserving f (rightAction_preserving hG y)).trans ?_
  exact Filter.Eventually.of_forall fun x => congrArg (f : Q → ℂ) (rightAction_out y x)

omit [LocallyOfFiniteType G.X.hom] in
private theorem continuous_rightAction :
    Continuous (fun a : AdelicGroupPoints F G × Q => LeftCosetSpace.rightTranslate Γ a.1 a.2) :=
  continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_fst).prodMk continuous_snd)

/-- Joint continuity of positive right translation in the adelic element and the `L²` class. -/
theorem continuous_rationalQuotientL2RightAction (hG : IsConnectedReductive G) :
    Continuous (fun a : AdelicGroupPoints F G × H => rationalQuotientL2RightAction hG a.1 a.2) := by
  let r : C(AdelicGroupPoints F G × Q, Q) := ⟨_, continuous_rightAction⟩
  exact continuous_snd.compMeasurePreservingLp
    (r.curry.continuous.comp continuous_fst) (fun a => rightAction_preserving hG a.1) (by simp)

section CompactAverage

variable (hG : IsConnectedReductive G) (K : Subgroup (AdelicGroupPoints F G))
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))

local notation "dk" => compactHaarProbability F G K hKc

private theorem rightAction_compact_aestronglyMeasurable (f : H) :
    AEStronglyMeasurable (fun k : K => rationalQuotientL2RightAction hG k.val f) dk := by
  let : SecondCountableTopology K :=
    inferInstanceAs (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  exact ((continuous_rationalQuotientL2RightAction hG).comp
    (continuous_subtype_val.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable

/-- Averaging positive right translates with an integrable weight on the supplied compact
subgroup, as a continuous linear map on the actual rational quotient `L²`. -/
def rationalQuotientL2CompactAverage (a : K → ℂ) (ha : Integrable a dk) : H →L[ℂ] H :=
  Langlands.Analysis.integratedIsometricAction dk
    ((rationalQuotientL2RightAction hG).comp K.subtype)
    (fun k f => norm_rationalQuotientL2RightAction hG k.val f)
    (rightAction_compact_aestronglyMeasurable hG K hKc) a ha

/-- The integrated right action is represented by its weighted pointwise average almost
everywhere. This holds for every `L²` vector without assuming a continuous representative. -/
theorem coeFn_rationalQuotientL2CompactAverage (a : K → ℂ) (ha : Integrable a dk) (f : H) :
    (∀ᵐ (x : Q) ∂μQ,
      Integrable (fun k : K => a k * f (LeftCosetSpace.mk Γ (x.out * k.val))) dk) ∧
    (rationalQuotientL2CompactAverage hG K hKc a ha f : Q → ℂ) =ᵐ[μQ]
      fun (x : Q) => ∫ k : K, a k * f (LeftCosetSpace.mk Γ (x.out * k.val)) ∂dk := by
  let : SecondCountableTopology K :=
    inferInstanceAs (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  have hm : Measurable (fun p : Q × K => LeftCosetSpace.rightTranslate Γ p.2.val p.1) :=
    (continuous_rightAction.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      continuous_fst)).measurable
  simpa only [rightAction_out, rationalQuotientL2CompactAverage] using
    Langlands.Analysis.integratedTranslationPointwise Q μQ K dk
      (fun x k => LeftCosetSpace.rightTranslate Γ k.val x) hm
      (fun k => rightAction_preserving hG k.val)
      ((rationalQuotientL2RightAction hG).comp K.subtype)
      (fun k v => norm_rationalQuotientL2RightAction hG k.val v)
      (rightAction_compact_aestronglyMeasurable hG K hKc)
      (fun k v => Lp.coeFn_compMeasurePreserving v (rightAction_preserving hG k.val)) a ha f

end CompactAverage

end Langlands.Global.AdelicGroupPoints
