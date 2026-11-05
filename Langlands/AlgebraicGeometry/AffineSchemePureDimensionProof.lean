import Langlands.AlgebraicGeometry.AffineSchemePureDimensionStatement
import Langlands.AlgebraicGeometry.FiniteTypePureDimensionProof

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Transfer the actual finite-type tensor comparison to any affine scheme over a field. -/
theorem hasPureDimension_affine_fieldExtension_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (d : ℕ) :
    HasPureDimension X d ↔
      HasPureDimension (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) d := by
  let : Algebra k Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, ⊤) := affineStructureMap_finiteType f
  exact hasPureDimension_iff_globalSections X |>.trans
    ((hasPureRingDimension_tensorProduct_iff k K Γ(X, ⊤) d).trans
      (hasPureDimension_affinePullback_iff K f d).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Use the actual residue-field extension of a cartesian scheme square. -/
theorem hasPureDimension_affine_fiberBaseChange_iff
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffineHom f] [LocallyOfFiniteType f]
    (h : IsPullback a b f g) (y : Y) (d : ℕ) :
    HasPureDimension (b.fiber y) d ↔ HasPureDimension (f.fiber (g y)) d := by
  let : Algebra (Z.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact (hasPureDimension_fiberBaseChange_iff h y d).trans
    (hasPureDimension_affine_fieldExtension_iff (Z.residueField (g y))
      (Y.residueField y) (f.fiber (g y)) (f.fiberToSpecResidueField (g y)) d).symm

/-- The exact grouped target. -/
theorem affineSchemePureDimensionComparisons :
    AffineSchemePureDimensionComparisons.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro k K _ _ _ X _ f _ d
    exact hasPureDimension_affine_fieldExtension_iff k K X f d
  · intro P X Y Z a b f g _ _ h y d
    exact hasPureDimension_affine_fiberBaseChange_iff h y d
  · intro P X Y Z a b f g _ _ h d
    have preserve : HasPureDimensionFibers d f → HasPureDimensionFibers d b :=
      fun hf y => (hasPureDimension_affine_fiberBaseChange_iff h y d).mpr (hf (g y))
    refine ⟨preserve, fun hg => ⟨?_, preserve⟩⟩
    intro hb z
    obtain ⟨y, rfl⟩ := hg.surj z
    exact (hasPureDimension_affine_fiberBaseChange_iff h y d).mp (hb y)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
