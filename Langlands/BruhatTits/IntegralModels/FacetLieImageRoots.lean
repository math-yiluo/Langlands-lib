import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.Lie.Functoriality

/-! # Lie-image weights of a torus-containing subgroup are its roots

For a torus `t : S ⟶ H` and a monomorphic inclusion `j : H ⟶ Q`, the nonzero
weights of `S` (through `t ≫ j`) on the differential image of `j` are exactly
the roots of `S` on `Lie(H)`. Applied to the special-fibre torus factored
through the actual reductive image, this rewrites the left side of the KP
facet sign formula as a set of roots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section LieImage

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

/-- For a monomorphic inclusion, the part of an ambient weight space lying in
the differential image is the image of the corresponding weight space. -/
theorem weightSpace_comp_inf_range_eq_map (t : S.toGrp ⟶ H) (j : H ⟶ Q)
    [Mono j.hom.hom] (χ : characterLattice S) :
    weightSpace (t ≫ j) χ ⊓ LinearMap.range (Lie.targetMapLinear j k) =
      (weightSpace t χ).map (Lie.targetMapLinear j k) := by
  ext y
  simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, (lieKernelHomLinear_mem_weightSpace_iff j t χ x).mp hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨lieKernelHomLinear_mem_weightSpace j t χ hx, x, rfl⟩

/-- The nonzero Lie-image weights of a monomorphic inclusion containing the
torus are exactly the roots of the torus in the subgroup. -/
theorem nonzeroLieImageWeights_comp_eq_roots (t : S.toGrp ⟶ H) (j : H ⟶ Q)
    [Mono j.hom.hom] :
    nonzeroLieImageWeights (t ≫ j) j = roots t := by
  ext χ
  change (χ ≠ 0 ∧ _ ≠ ⊥) ↔ (χ ≠ 0 ∧ _ ≠ ⊥)
  rw [weightSpace_comp_inf_range_eq_map, ← Submodule.map_bot (Lie.targetMapLinear j k),
    (Submodule.map_injective_of_injective (Lie.targetMapLinear_injective j k)).ne_iff]

end LieImage

namespace RelativeComponentModelHom

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData source S i)

attribute [local instance] neutralSpecialFibre_affine neutralSpecialFibre_isAffine
  quotient_isAffine

/-- The special-fibre torus, mapped into the actual reductive image `℘_F(F')`
through the schematic-image projection. -/
def reductiveImageTorusMap : T.specialFibre.toGrp ⟶ φ.reductiveImage Q :=
  T.specialFibreInclusion ≫ SchematicImage.projection (φ.neutralSpecialFibreMap ≫ Q.projection)

/-- The torus image in the quotient factors through the actual reductive image. -/
theorem reductiveImageTorusMap_comp_inclusion :
    φ.reductiveImageTorusMap Q T ≫ φ.reductiveImageInclusion Q =
      φ.quotientTorusInclusion Q T := by
  unfold reductiveImageTorusMap quotientTorusInclusion targetTorusInclusion
  rw [Category.assoc, SchematicImage.projection_inclusion, Category.assoc]

local instance reductiveImageInclusion_mono :
    Mono (φ.reductiveImageInclusion Q).hom.hom :=
  inferInstanceAs (Mono (SchematicImage.inclusionOver _))

/-- The left side of the KP facet sign formula is the root set of the
special-fibre torus in the actual reductive image `℘_F(F')`. -/
theorem nonzeroLieImageWeights_quotientTorusInclusion :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      roots (φ.reductiveImageTorusMap Q T) := by
  rw [← φ.reductiveImageTorusMap_comp_inclusion Q T]
  exact nonzeroLieImageWeights_comp_eq_roots _ _

end RelativeComponentModelHom

end Langlands.BruhatTits.IntegralModels
