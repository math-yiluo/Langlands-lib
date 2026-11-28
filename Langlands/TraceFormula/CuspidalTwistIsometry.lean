import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.TraceFormula.GroupSchemeTwistCuspidalInvarianceProof
import Langlands.TraceFormula.IsotypicTrace.TwistCovariance

/-! # The algebraic twist on the cuspidal Hilbert space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

namespace Langlands.TraceFormula

/-- The measure-preserving pullback by an algebraic automorphism of the adelic quotient
restricts to a linear isometric equivalence of the full cuspidal subspace, intertwining
right translation by `a` with right translation by the image of `a`. -/
def CuspidalTwistIsometryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (α : G ≅ G) (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G),
    (∀ x, Θ x = AdelicGroupPoints.map F G G α.hom x) →
    let Γ := positiveRationalSubgroup F G Z i
    let mQ := positiveRationalQuotientHaarMeasure F G Z i
    let S := fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hc
    let π := fullAEL2CuspidalBoundedRightAction F G hPD hG Z i hi I e hc
    ∀ (hΘ : ∀ x, Θ x ∈ Γ ↔ x ∈ Γ)
      (hmQ : MeasurePreserving (quotientAutomorphism Γ Θ hΘ).symm mQ mQ),
      ∃ U : S ≃ₗᵢ[ℂ] S,
        (∀ x : S, (U x : Lp ℂ 2 mQ) = twistOperator Γ Θ hΘ mQ hmQ x) ∧
        ∀ a x, U (π a x) = π (Θ a) (U x)

private theorem compMeasurePreserving_congr {X : Type*} [MeasurableSpace X] {mQ : Measure X}
    {f g : X → X} (hf : MeasurePreserving f mQ mQ) (hg : MeasurePreserving g mQ mQ)
    (h : f = g) (x : Lp ℂ 2 mQ) :
    Lp.compMeasurePreserving f hf x = Lp.compMeasurePreserving g hg x := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem cuspidalTwistIsometry : CuspidalTwistIsometryStatement.{u} := by
  intro F _ _ G _ _ hPD hG Z i hi _ I _ e hc _ α Θ hα Γ mQ S π hΘ hmQ
  let := positiveRationalQuotient_borelSpace F G Z i hi I e hc
  let q := (quotientAutomorphism Γ Θ hΘ).toMeasurableEquiv
  have hq : MeasurePreserving q mQ mQ := MeasurePreserving.symm q.symm hmQ
  have hΘ' (x) : Θ.symm x ∈ Γ ↔ x ∈ Γ := by
    simpa only [Θ.apply_symm_apply] using (hΘ (Θ.symm x)).symm
  have hα' (x) : Θ.symm x = AdelicGroupPoints.map F G G α.inv x := by
    apply Θ.injective
    rw [Θ.apply_symm_apply, hα]
    simp only [AdelicGroupPoints.map_apply, GroupScheme.affinePointsTarget_apply,
      Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hq' : ⇑(quotientAutomorphism Γ Θ.symm hΘ').symm = ⇑q := by
    funext x
    induction x using Quotient.inductionOn with
    | _ x => rfl
  have hmQ' : MeasurePreserving (quotientAutomorphism Γ Θ.symm hΘ').symm mQ mQ := by
    rw [hq']
    exact hq
  let A := twistOperator Γ Θ hΘ mQ hmQ
  let A' := twistOperator Γ Θ.symm hΘ' mQ hmQ'
  have hA := groupSchemeTwistCuspidalInvariance F G hPD hG Z i hi I e hc α Θ hα hΘ hmQ
  have hA' := groupSchemeTwistCuspidalInvariance F G hPD hG Z i hi I e hc α.symm Θ.symm hα' hΘ' hmQ'
  have hA'_eq (x : Lp ℂ 2 mQ) : A' x = Lp.compMeasurePreserving q hq x :=
    compMeasurePreserving_congr hmQ' hq hq' x
  let B : S →ₗᵢ[ℂ] S :=
    ⟨A.toLinearMap.restrict hA, fun x => norm_twistOperator_apply Γ Θ hΘ mQ hmQ x⟩
  let B' : S →ₗ[ℂ] S := A'.toLinearMap.restrict hA'
  let U : S ≃ₗᵢ[ℂ] S := LinearIsometryEquiv.ofLinearIsometry B B'
    (LinearMap.ext fun x => by
      apply Subtype.ext
      change A (A' x) = (x : Lp ℂ 2 mQ)
      rw [hA'_eq]
      change Lp.compMeasurePreserving q.symm hmQ
        (Lp.compMeasurePreserving q hq (x : Lp ℂ 2 mQ)) = _
      rw [← Lp.compMeasurePreserving_comp_apply,
        compMeasurePreserving_congr _ (MeasurePreserving.id mQ) q.self_comp_symm]
      exact Lp.compMeasurePreserving_id_apply (x : Lp ℂ 2 mQ))
    (LinearMap.ext fun x => by
      apply Subtype.ext
      change A' (A x) = (x : Lp ℂ 2 mQ)
      rw [hA'_eq]
      change Lp.compMeasurePreserving q hq
        (Lp.compMeasurePreserving q.symm hmQ (x : Lp ℂ 2 mQ)) = _
      rw [← Lp.compMeasurePreserving_comp_apply,
        compMeasurePreserving_congr _ (MeasurePreserving.id mQ) q.symm_comp_self]
      exact Lp.compMeasurePreserving_id_apply (x : Lp ℂ 2 mQ))
  refine ⟨U, fun _ => rfl, fun a x => ?_⟩
  apply Subtype.ext
  exact IsotypicTrace.twistOperator_quotientL2RightTranslate F G Z i mQ
    (haarQuotientMeasureRightInvariant F G Z i hi I e hc) Θ hΘ hmQ a x

end Langlands.TraceFormula
