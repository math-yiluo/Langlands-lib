import Langlands.GroupScheme.IdentityComponentRationalQuotient
import Langlands.GroupScheme.IdentityComponent.Transport

/-! # Functoriality of the rational identity-component quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k]
  {H H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- An actual group-scheme homomorphism preserves identity-component rational points. -/
theorem comp_mem_rationalIdentitySubgroup (f : H ⟶ H')
    {x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X}
    (hx : x ∈ rationalIdentitySubgroup H) :
    x ≫ f.hom.hom ∈ rationalIdentitySubgroup H' := by
  rcases (mem_rationalIdentitySubgroup H x).mp hx with ⟨y, rfl⟩
  apply (mem_rationalIdentitySubgroup H' _).mpr
  refine ⟨y ≫ (map f).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, map_identityComponentι,
    Grp.comp_hom_hom, ← Category.assoc]

/-- The homomorphism on ordinary rational-component quotients induced by an actual map. -/
def rationalComponentMap (f : H ⟶ H') :
    RationalComponentQuotient H →* RationalComponentQuotient H' :=
  rationalComponentLift H
    ((rationalComponentProjection H').comp
      ((pointsMap f).app (op (𝟙_ (Over (Spec (CommRingCat.of k)))))).hom)
    (by
      intro x hx
      change rationalComponentProjection H' (x ≫ f.hom.hom) = 1
      apply MonoidHom.mem_ker.mp
      rw [ker_rationalComponentProjection]
      exact comp_mem_rationalIdentitySubgroup f hx)

@[simp]
theorem rationalComponentMap_projection (f : H ⟶ H')
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    rationalComponentMap f (rationalComponentProjection H x) =
      rationalComponentProjection H' (x ≫ f.hom.hom) :=
  rfl

/-- Maps out of the rational quotient are determined on projected rational points. -/
theorem rationalComponentHom_ext {M : Type*} [Group M]
    {f g : RationalComponentQuotient H →* M}
    (h : ∀ x, f (rationalComponentProjection H x) =
      g (rationalComponentProjection H x)) : f = g := by
  ext c
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  exact h x

@[simp]
theorem rationalComponentMap_id :
    rationalComponentMap (𝟙 H) = MonoidHom.id (RationalComponentQuotient H) := by
  apply rationalComponentHom_ext
  intro x
  simp

@[simp]
theorem rationalComponentMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    rationalComponentMap (f ≫ g) =
      (rationalComponentMap g).comp (rationalComponentMap f) := by
  apply rationalComponentHom_ext
  intro x
  simp [Category.assoc]

/-- The quotient embedding commutes with the continuous map on actual scheme components. -/
theorem rationalComponentEmbedding_naturality (f : H ⟶ H')
    (c : RationalComponentQuotient H) :
    rationalComponentEmbedding H' (rationalComponentMap f c) =
      f.hom.hom.left.continuous.connectedComponentsMap (rationalComponentEmbedding H c) := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  rfl

/-- An actual group-scheme isomorphism induces an equivalence of rational-component groups. -/
def rationalComponentEquiv (e : H ≅ H') :
    RationalComponentQuotient H ≃* RationalComponentQuotient H' where
  toFun := rationalComponentMap e.hom
  invFun := rationalComponentMap e.inv
  left_inv := by
    intro c
    change ((rationalComponentMap e.inv).comp (rationalComponentMap e.hom)) c = c
    rw [← rationalComponentMap_comp, e.hom_inv_id, rationalComponentMap_id]
    rfl
  right_inv := by
    intro c
    change ((rationalComponentMap e.hom).comp (rationalComponentMap e.inv)) c = c
    rw [← rationalComponentMap_comp, e.inv_hom_id, rationalComponentMap_id]
    rfl
  map_mul' := (rationalComponentMap e.hom).map_mul

@[simp]
theorem rationalComponentEquiv_toMonoidHom (e : H ≅ H') :
    (rationalComponentEquiv e).toMonoidHom = rationalComponentMap e.hom :=
  rfl

@[simp]
theorem rationalComponentEquiv_projection (e : H ≅ H')
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    rationalComponentEquiv e (rationalComponentProjection H x) =
      rationalComponentProjection H' (x ≫ e.hom.hom.hom) :=
  rfl

@[simp]
theorem rationalComponentEquiv_symm (e : H ≅ H') :
    (rationalComponentEquiv e).symm = rationalComponentEquiv e.symm := by
  ext c
  rfl

end Langlands.GroupScheme.IdentityComponent
