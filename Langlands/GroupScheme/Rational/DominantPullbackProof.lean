import Langlands.GroupScheme.Rational.DominantPullbackStatement

/-! # Proof that dominant affine maps have injective actual coordinate pullback -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.PointedCoordinateWeights

variable {k : Type u} [Field k] {V W : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [IsAffineHom W.hom]

/-- The chosen coordinate isomorphisms identify `Spec` of the actual pullback with `f`. -/
theorem algSpec_map_pullback (f : V ⟶ W) :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (pullback f)).op ≫
        (coordinateIso W).hom = (coordinateIso V).hom ≫ f := by
  have h : pointCoordinates.symm (pullback f) = universalPoint V ≫ f :=
    pointCoordinates.symm_apply_apply _
  have hu : universalPoint V = (coordinateIso V).hom := by
    change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (AlgHom.id k (Coord V))).op ≫
      (coordinateIso V).hom = _
    rw [CommAlgCat.ofHom_id, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← hu]
  exact h

/-- A dominant morphism of affine schemes with reduced target has injective
actual coordinate pullback, via scheme-theoretic dominance of its `Spec`. -/
theorem dominantPullbackStatement : DominantPullbackStatement.{u} := by
  intro k _ V W _ _ f hW hf
  -- The ring map underlying the actual pullback.
  let ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom (pullback f))).right
  have hψ : Spec.map ψ =
      (coordinateIso V).hom.left ≫ f.left ≫ (coordinateIso W).inv.left := by
    have h := congrArg CommaMorphism.left (algSpec_map_pullback f)
    simp only [Over.comp_left, algSpec_map_left] at h
    rw [← Category.assoc, ← h, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.comp_id]
    rfl
  have : IsReduced (Spec ((commAlgCatEquivUnder (CommRingCat.of k)).functor.obj
      (Coord W)).right) :=
    isReduced_of_isOpenImmersion (coordinateIso W).hom.left
  have : IsDominant (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  have : IsSchemeTheoreticallyDominant (Spec.map ψ) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have happ : Function.Injective (Spec.map ψ).appTop := (Spec.map ψ).app_injective ⊤
  have hψeq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso _).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hinj : Function.Injective ψ.hom := by
    rw [hψeq, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective.comp
      (happ.comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective)
  intro x y hxy
  exact hinj hxy

end Langlands.GroupScheme.PointedCoordinateWeights
