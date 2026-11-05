import Langlands.GroupScheme.IntegralModel

/-! # Compatible integral-model isomorphisms and original point images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) (N : IntegralModel R K H) (f : G ≅ H)

/-- An isomorphism of actual integral models compatible with their supplied
generic identifications and the specified generic-group isomorphism. -/
structure Iso where
  iso : M.group ≅ N.group
  generic_comm :
    (GroupScheme.baseChange (Spec.algebraMap R K)).map iso.hom ≫ N.genericIso.hom =
      M.genericIso.hom ≫ f.hom

namespace Iso

variable {M N f}

/-- Regard a compatible model isomorphism as the existing model homomorphism. -/
def toHom (e : M.Iso N f) : M.Hom N f.hom :=
  ⟨e.iso.hom, e.generic_comm⟩

/-- The induced equivalence uses the actual integral sections of both models. -/
def integralSectionsEquiv (e : M.Iso N f) :
    M.integralSections ≃* N.integralSections where
  toFun := rationalPoints.map e.iso.hom
  invFun := rationalPoints.map e.iso.inv
  left_inv x := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      e.iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv x := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      e.iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_mul' := map_mul _

/-- Original integral-point maps commute with the compatible model isomorphism. -/
theorem integralPointMap_naturality (e : M.Iso N f) (x : M.integralSections) :
    N.integralPointMap (e.integralSectionsEquiv x) =
      rationalPoints.map f.hom (M.integralPointMap x) :=
  e.toHom.integralPointMap_naturality x

/-- A compatible model isomorphism transports exactly the original subgroup image. -/
theorem map_integralPoints (e : M.Iso N f) :
    M.integralPoints.map (rationalPoints.map f.hom) = N.integralPoints := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact e.toHom.map_mem_integralPoints hx
  · rintro ⟨y, rfl⟩
    refine ⟨M.integralPointMap (e.integralSectionsEquiv.symm y),
      ⟨e.integralSectionsEquiv.symm y, rfl⟩, ?_⟩
    rw [← e.integralPointMap_naturality, MulEquiv.apply_symm_apply]

/-- For a fixed generic group and its identity map, the original images are equal. -/
theorem integralPoints_eq {N : IntegralModel R K G}
    (e : M.Iso N (CategoryTheory.Iso.refl G)) :
    M.integralPoints = N.integralPoints := by
  have hid : rationalPoints.map (𝟙 G) = MonoidHom.id (rationalPoints G) := by
    ext x
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id,
      MonoidHom.id_apply]
  have h := e.map_integralPoints
  change M.integralPoints.map (rationalPoints.map (𝟙 G)) = N.integralPoints at h
  rw [hid, Subgroup.map_id] at h
  exact h

end Iso

end Langlands.GroupScheme.IntegralModel
