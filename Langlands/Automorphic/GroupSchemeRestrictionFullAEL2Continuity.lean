import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2Continuity
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-! # Joint continuity and integrated action on the almost-everywhere cuspidal `L²` subspace
of `[G]` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.QuotientIntegration
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)

section Canonical

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "μ" => quotientHaarMeasure F G S j
local notation "Sq" => quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
local notation "ρ" => rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv'
local notation "ρc" => quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv'

set_option maxRecDepth 20000 in
/-- The published joint right action on `L²([G])`, restricted to the cuspidal subspace. -/
def quotientFullAEL2CuspidalJointRightAction : C(AdelicGroupPoints F G × Sq, Sq) where
  toFun aφ := ρc aφ.1 aφ.2
  continuous_toFun :=
    ((rationalQuotientL2JointRightAction F G hInv' h hi hc hT).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp]
theorem quotientFullAEL2CuspidalJointRightAction_apply (a : AdelicGroupPoints F G) (φ : Sq) :
    quotientFullAEL2CuspidalJointRightAction F G hPD hG h hi hc hT hInv' (a, φ) = ρc a φ := rfl

/-- Forgetting the subtype recovers the published joint action on `L²([G])`. -/
theorem quotientFullAEL2CuspidalJointRightAction_val (a : AdelicGroupPoints F G) (φ : Sq) :
    (quotientFullAEL2CuspidalJointRightAction F G hPD hG h hi hc hT hInv' (a, φ)).val =
      rationalQuotientL2JointRightAction F G hInv' h hi hc hT (a, φ.val) := rfl

/-- The continuous orbit map of a cuspidal vector. -/
def quotientFullAEL2CuspidalOrbitMap (φ : Sq) : C(AdelicGroupPoints F G, Sq) :=
  (quotientFullAEL2CuspidalJointRightAction F G hPD hG h hi hc hT hInv').comp
    ⟨fun a => (a, φ), continuous_id.prodMk continuous_const⟩

@[simp]
theorem quotientFullAEL2CuspidalOrbitMap_apply (φ : Sq) (a : AdelicGroupPoints F G) :
    quotientFullAEL2CuspidalOrbitMap F G hPD hG h hi hc hT hInv' φ a = ρc a φ := rfl

/-- The cuspidal right action, bundled by the bounded maps of its isometries. -/
def quotientFullAEL2CuspidalBoundedRightAction : AdelicGroupPoints F G →* (Sq →L[ℂ] Sq) where
  toFun a :=
    (quotientFullAEL2CuspidalRightTranslate F G hPD hG h hi hc hT hInv' a).toLinearIsometry
      |>.toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact rationalQuotientL2RightTranslate_one F G μ hInv' φ.val
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro φ
    apply Subtype.ext
    exact rationalQuotientL2RightTranslate_mul F G μ hInv' a b φ.val

@[simp]
theorem quotientFullAEL2CuspidalBoundedRightAction_apply (a : AdelicGroupPoints F G) (φ : Sq) :
    quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv' a φ = ρc a φ := rfl

theorem norm_quotientFullAEL2CuspidalBoundedRightAction (a : AdelicGroupPoints F G) (φ : Sq) :
    ‖quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv' a φ‖ = ‖φ‖ :=
  norm_quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv' a φ

local notation "πc" => quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv'
local notation "hπcnorm" =>
  norm_quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv'

section Integrated

variable (ν : Measure (AdelicGroupPoints F G))

/-- Cuspidal orbits are strongly measurable for every supplied group measure. -/
theorem quotientFullAEL2CuspidalOrbit_aestronglyMeasurable (φ : Sq) :
    AEStronglyMeasurable (fun a => πc a φ) ν :=
  (quotientFullAEL2CuspidalOrbitMap F G hPD hG h hi hc hT hInv' φ).continuous.stronglyMeasurable
    |>.aestronglyMeasurable

local notation "hπcmeas" =>
  quotientFullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG h hi hc hT hInv' ν

variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

include hf in
/-- Absolute Bochner convergence of the weighted cuspidal orbit. -/
theorem quotientFullAEL2CuspidalActionIntegrand_integrable (φ : Sq) :
    Integrable (fun a => f a • ρc a φ) ν :=
  isometricActionIntegrand_integrable ν πc hπcnorm hπcmeas f hf φ

local notation "A" => rationalQuotientL2IntegratedAction F G hInv' h hi hc hT ν f hf

/-- The Bochner integral of a weighted cuspidal orbit, computed in the cuspidal subspace, is the
published integrated action on `L²([G])`. -/
theorem coe_integral_quotientFullAEL2CuspidalRightAction (φ : Sq) :
    ((∫ g, f g • ρc g φ ∂ν : Sq) : Lp ℂ 2 μ) = A φ := by
  rw [rationalQuotientL2IntegratedAction_apply]
  exact ((Sq).subtypeₗᵢ.integral_comp_comm (fun g => f g • ρc g φ)).symm

/-- The published integrated action maps the cuspidal subspace into itself. -/
theorem rationalQuotientL2IntegratedAction_mem_quotientFullAEL2CuspidalSubmodule
    (φ : Lp ℂ 2 μ) (hφ : φ ∈ Sq) : A φ ∈ Sq := by
  rw [← coe_integral_quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv' ν f hf
    ⟨φ, hφ⟩]
  exact Submodule.coe_mem _

/-- The weighted right action `φ ↦ ∫ f(g) R(g) φ dν(g)` on the cuspidal subspace. -/
def quotientFullAEL2CuspidalIntegratedAction : Sq →L[ℂ] Sq :=
  ((A).comp (Sq).subtypeL).codRestrict Sq fun φ =>
    rationalQuotientL2IntegratedAction_mem_quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
      hInv' ν f hf φ.val φ.prop

/-- Forgetting the subtype recovers the published integrated action on `L²([G])`. -/
theorem quotientFullAEL2CuspidalIntegratedAction_val (φ : Sq) :
    (quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv' ν f hf φ).val =
      A φ.val := rfl

/-- The integrated cuspidal action is the Bochner integral of the weighted cuspidal orbit. -/
theorem quotientFullAEL2CuspidalIntegratedAction_apply (φ : Sq) :
    quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv' ν f hf φ =
      ∫ g, f g • ρc g φ ∂ν :=
  Subtype.ext
    (coe_integral_quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv' ν f hf φ).symm

theorem norm_quotientFullAEL2CuspidalIntegratedAction_le :
    ‖quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv' ν f hf‖ ≤
      ∫ g, ‖f g‖ ∂ν := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) ?_
  intro φ
  calc ‖quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv' ν f hf φ‖ =
        ‖A φ.val‖ := rfl
    _ ≤ ‖A‖ * ‖φ.val‖ := (A).le_opNorm _
    _ ≤ (∫ g, ‖f g‖ ∂ν) * ‖φ‖ := mul_le_mul_of_nonneg_right
        (norm_rationalQuotientL2IntegratedAction_le F G hInv' h hi hc hT ν f hf) (norm_nonneg _)

/-- The orthogonal projection onto the cuspidal subspace intertwines the integrated actions. -/
theorem quotientFullAEL2CuspidalOrthogonalProjection_integratedAction (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT (A φ) =
      quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv' ν f hf
        (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ) := by
  let P := quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT
  rw [quotientFullAEL2CuspidalIntegratedAction_apply, rationalQuotientL2IntegratedAction_apply,
    ← P.integral_comp_comm
      (rationalQuotientL2ActionIntegrand_integrable F G hInv' h hi hc hT ν f hf φ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change P (f a • ρ a φ) = f a • ρc a (P φ)
    rw [map_smul]
    exact congrArg (fun ψ => f a • ψ)
      (quotientFullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG h hi hc hT hInv' a φ)

/-- The ambient orthogonal projection onto the cuspidal subspace commutes with the integrated
action on `L²([G])`. -/
theorem quotientFullAEL2CuspidalAmbientProjection_integratedAction (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT (A φ) =
      A (quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ) :=
  congrArg Subtype.val
    (quotientFullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG h hi hc hT hInv'
      ν f hf φ)

end Integrated

end Canonical

section Comparison

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
variable (ν : Measure (AdelicGroupPoints F G))
variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

/-- The isometric isomorphism `fullAEL2CuspidalEquiv` intertwines the published integrated
positive-torus cuspidal action with the integrated cuspidal action on `[G]`. -/
theorem fullAEL2CuspidalEquiv_integratedAction
    (φ : fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    fullAEL2CuspidalEquiv F G hPD hG h hi I e hc
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf φ) =
      quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩ hInv'
        ν f hf (fullAEL2CuspidalEquiv F G hPD hG h hi I e hc φ) :=
  Subtype.ext ((congrArg (quotientL2Equiv F G h)
    (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν f hf φ)).trans
      (quotientL2Equiv_integratedAction F G hInv' h hi hc ⟨I, inferInstance, ⟨e⟩⟩ ν f hf I e
        φ.val))

end Comparison

section SplitComponents

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

local notation "hInvS" => quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs
local notation "hS" => subgroup_eq_of_splitComponents F G hj hs
local notation "Ss" => splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs

/-- For split components, the joint right action on the cuspidal subspace. -/
def splitComponentFullAEL2CuspidalJointRightAction : C(AdelicGroupPoints F G × Ss, Ss) :=
  quotientFullAEL2CuspidalJointRightAction F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS

/-- Forgetting the subtype recovers the published split-component joint action. -/
theorem splitComponentFullAEL2CuspidalJointRightAction_val (a : AdelicGroupPoints F G)
    (φ : Ss) :
    (splitComponentFullAEL2CuspidalJointRightAction F G hPD hG hi hj hs (a, φ)).val =
      splitComponentL2JointRightAction F G hi hj hs (a, φ.val) := rfl

variable (ν : Measure (AdelicGroupPoints F G))
variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

/-- For split components, the weighted right action on the cuspidal subspace. -/
def splitComponentFullAEL2CuspidalIntegratedAction : Ss →L[ℂ] Ss :=
  quotientFullAEL2CuspidalIntegratedAction F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS ν f hf

/-- Forgetting the subtype recovers the published split-component integrated action. -/
theorem splitComponentFullAEL2CuspidalIntegratedAction_val (φ : Ss) :
    (splitComponentFullAEL2CuspidalIntegratedAction F G hPD hG hi hj hs ν f hf φ).val =
      splitComponentL2IntegratedAction F G hi hj hs ν f hf φ.val := rfl

theorem norm_splitComponentFullAEL2CuspidalIntegratedAction_le :
    ‖splitComponentFullAEL2CuspidalIntegratedAction F G hPD hG hi hj hs ν f hf‖ ≤
      ∫ g, ‖f g‖ ∂ν :=
  norm_quotientFullAEL2CuspidalIntegratedAction_le F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS ν f hf

/-- For split components, the orthogonal cuspidal projection intertwines the integrated
actions. -/
theorem splitComponentFullAEL2CuspidalOrthogonalProjection_integratedAction
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    splitComponentFullAEL2CuspidalOrthogonalProjection F G hPD hG hi hj hs
        (splitComponentL2IntegratedAction F G hi hj hs ν f hf φ) =
      splitComponentFullAEL2CuspidalIntegratedAction F G hPD hG hi hj hs ν f hf
        (splitComponentFullAEL2CuspidalOrthogonalProjection F G hPD hG hi hj hs φ) :=
  quotientFullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG hS hi hs.1.2 hs.1.1.1
    hInvS ν f hf φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
