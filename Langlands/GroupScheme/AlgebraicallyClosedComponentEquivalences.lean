import Langlands.GroupScheme.AlgebraicallyClosedComponentBaseChangeProof
import Langlands.GroupScheme.GaloisPointTowerBaseChange

/-! # Actual component equivalences and field-tower compatibility -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

section Isomorphism

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- An actual group-scheme isomorphism induces an equivalence on all components. -/
def allComponentIso (i : H ≅ H') :
    AlgebraicallyClosedComponents H ≃* AlgebraicallyClosedComponents H' where
  toFun := allComponentMap i.hom
  invFun := allComponentMap i.inv
  left_inv c := by
    change ((allComponentMap i.inv).comp (allComponentMap i.hom)) c = c
    rw [← allComponentMap_comp, i.hom_inv_id, allComponentMap_id]
    rfl
  right_inv c := by
    change ((allComponentMap i.hom).comp (allComponentMap i.inv)) c = c
    rw [← allComponentMap_comp, i.inv_hom_id, allComponentMap_id]
    rfl
  map_mul' := (allComponentMap i.hom).map_mul

@[simp]
theorem allComponentIso_apply (i : H ≅ H') (c : AlgebraicallyClosedComponents H) :
    allComponentIso i c = allComponentMap i.hom c :=
  rfl

end Isomorphism

section Extension

variable {k L : Type u} [Field k] [Field L] [IsAlgClosed k] [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom] (φ : k →+* L)

/-- The published extension homomorphism as an equivalence of actual component groups. -/
def allComponentBaseChangeEquiv :
    AlgebraicallyClosedComponents H ≃*
      AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H) :=
  MulEquiv.ofBijective (allComponentBaseChange H φ)
    (algebraicallyClosedComponentBaseChange k L H φ)

@[simp]
theorem allComponentBaseChangeEquiv_apply (c : AlgebraicallyClosedComponents H) :
    allComponentBaseChangeEquiv H φ c = allComponentBaseChange H φ c :=
  rfl

/-- Its inverse is the continuous map on components of the actual projection. -/
theorem allComponentBaseChangeEquiv_symm_apply
    (c : AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H)) :
    (allComponentBaseChangeEquiv H φ).symm c =
      (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap c := by
  obtain ⟨a, rfl⟩ := (allComponentBaseChangeEquiv H φ).surjective c
  rw [MulEquiv.symm_apply_apply, allComponentBaseChangeEquiv_apply,
    allComponentBaseChange_fst]

/-- Projection is a group homomorphism on all actual components. -/
def allComponentProjection :
    AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H) →*
      AlgebraicallyClosedComponents H :=
  (allComponentBaseChangeEquiv H φ).symm.toMonoidHom

theorem allComponentProjection_apply
    (c : AlgebraicallyClosedComponents ((GroupScheme.baseChange (specMap φ)).obj H)) :
    allComponentProjection H φ c =
      (pullback.fst H.X.hom (specMap φ)).continuous.connectedComponentsMap c :=
  allComponentBaseChangeEquiv_symm_apply H φ c

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- The extension equivalences are natural in actual group-scheme homomorphisms. -/
theorem allComponentBaseChangeEquiv_naturality (f : H ⟶ H')
    (c : AlgebraicallyClosedComponents H) :
    allComponentMap ((GroupScheme.baseChange (specMap φ)).map f)
        (allComponentBaseChangeEquiv H φ c) =
      allComponentBaseChangeEquiv H' φ (allComponentMap f c) :=
  congrArg (fun m => m c) (allComponentBaseChange_naturality φ f)

end Extension

section Tower

open GaloisPointComparison

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [IsAlgClosed k] [IsAlgClosed L] [IsAlgClosed M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

omit [IsAlgClosed k] [IsAlgClosed L] in
/-- The actual tower isomorphism commutes with projection on all components. -/
theorem allComponentIso_tower_projection
    (c : AlgebraicallyClosedComponents (baseChanged L M (baseChanged k L H))) :
    (pullback.fst H.X.hom (baseMap k M)).continuous.connectedComponentsMap
        (allComponentIso (towerBaseChangeIso k L M H) c) =
      (pullback.fst H.X.hom (baseMap k L)).continuous.connectedComponentsMap
        ((pullback.fst (baseChanged k L H).X.hom (baseMap L M)).continuous.connectedComponentsMap
          c) := by
  rw [allComponentIso_apply, allComponentMap_apply]
  obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  simp only [Continuous.connectedComponentsMap_mk]
  exact congrArg _root_.ConnectedComponents.mk
    (congrArg (fun f => f p) (towerBaseChangeIso_hom_fst k L M H))

/-- Successive extensions agree with direct extension through the actual tower comparison. -/
theorem allComponentBaseChangeEquiv_tower (c : AlgebraicallyClosedComponents H) :
    allComponentIso (towerBaseChangeIso k L M H)
        (allComponentBaseChangeEquiv (baseChanged k L H) (algebraMap L M)
          (allComponentBaseChangeEquiv H (algebraMap k L) c)) =
      allComponentBaseChangeEquiv H (algebraMap k M) c := by
  apply componentProjection_injective_of_isAlgClosed H (algebraMap k M)
  rw [allComponentIso_tower_projection]
  simp only [allComponentBaseChangeEquiv_apply, allComponentBaseChange_fst]
  rfl

end Tower

end Langlands.GroupScheme.IdentityComponent
