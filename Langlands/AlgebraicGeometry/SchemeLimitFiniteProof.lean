import Langlands.AlgebraicGeometry.SchemeLimitFiniteStatement
import Langlands.Algebra.FilteredRingFinitenessProof

/-! # Proof of finite-morphism detection in affine scheme diagrams -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

theorem affineDiagramFiniteDescent :
    AffineDiagramFiniteDescent.{u} := by
  intro I _ _ E F _ _ α cE cF hcE hcF f hf i₀ _ hcart H
  let := H
  have : IsAffine cF.pt := Scheme.isAffine_of_isLimit cF hcF
  have (i : Iᵒᵖ) : IsAffine (E.op.obj i).unop := by dsimp; infer_instance
  have (i : Iᵒᵖ) : IsAffine (F.op.obj i).unop := by dsimp; infer_instance
  let A := F.op ⋙ Scheme.Γ
  let B := E.op ⋙ Scheme.Γ
  let β : A ⟶ B := Functor.whiskerRight (NatTrans.op α) Scheme.Γ
  let dA := Scheme.Γ.mapCocone cF.op
  let dB := Scheme.Γ.mapCocone cE.op
  have hcA : IsColimit dA := isColimitOfPreserves Scheme.Γ hcF.op
  have hcB : IsColimit dB := isColimitOfPreserves Scheme.Γ hcE.op
  have hw (i : Iᵒᵖ) : dA.ι.app i ≫ f.appTop = β.app i ≫ dB.ι.app i := by
    change (cF.π.app i.unop).appTop ≫ f.appTop =
      (α.app i.unop).appTop ≫ (cE.π.app i.unop).appTop
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop (hf i.unop).symm
  have hft : (β.app (op i₀)).hom.FiniteType := by
    change (α.app i₀).appTop.hom.FiniteType
    exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (α.app i₀) inferInstance
  have hpush {j : Iᵒᵖ} (r : op i₀ ⟶ j) :
      IsPushout (β.app (op i₀)) (A.map r) (B.map r) (β.app j) := by
    exact isPushout_appTop_of_isPullback (hcart r.unop)
  obtain ⟨j, r, hj⟩ := Langlands.Algebra.FilteredRing.finiteTypeFinitenessDescent
    A B β dA dB hcA hcB f.appTop hw (op i₀) hft hpush
    f.finite_appTop
  exact ⟨j.unop, r.unop, (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr ⟨inferInstance, hj⟩⟩

end Langlands.AlgebraicGeometry.AffineLimit
