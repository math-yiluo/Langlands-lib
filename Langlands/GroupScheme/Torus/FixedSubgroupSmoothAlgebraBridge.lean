import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine coordinate smoothness and a closed subgroup bridge -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable.FixedSubgroupSmoothAlgebraBridge

set_option backward.isDefEq.respectTransparency false

/-- Smooth affine group schemes have smooth coordinate algebras. -/
theorem coordinateAlgebra_smooth {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom] [Smooth G.X.hom] :
    Algebra.Smooth R (Lie.coordinateAlgebra G) := by
  have h : Smooth ((algSpec R).obj (op (Lie.coordinateAlgebra G))).hom := by
    have h' : Smooth ((Lie.coordinateIso G).hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h'
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap R (Lie.coordinateAlgebra G)))) at h
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

/-- Smoothness of the chosen coordinate algebra implies smoothness of the
original affine group scheme. -/
theorem smooth_of_coordinateAlgebra_smooth {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    [Algebra.Smooth R (Lie.coordinateAlgebra G)] : Smooth G.X.hom := by
  have h : Smooth ((algSpec R).obj (op (Lie.coordinateAlgebra G))).hom := by
    change Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap R (Lie.coordinateAlgebra G))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have := h
  have h' : Smooth ((Lie.coordinateIso G).inv.left ≫
      ((algSpec R).obj (op (Lie.coordinateAlgebra G))).hom) := inferInstance
  simpa only [Over.w] using h'

/-- An affine closed subgroup of a smooth affine group over a field is smooth
once its coordinate algebra is formally smooth. -/
theorem smooth_of_formallySmooth {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))} (j : C ⟶ G)
    [IsClosedImmersion j.hom.hom.left] [Smooth G.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom]
    (h : Algebra.FormallySmooth k (Lie.coordinateAlgebra C)) : Smooth C.X.hom := by
  have hC : LocallyOfFiniteType C.X.hom := by
    have h' : LocallyOfFiniteType (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h'
  have := hC
  have := h
  have : Algebra.FinitePresentation k (Lie.coordinateAlgebra C) :=
    Algebra.FinitePresentation.of_finiteType.mp (Lie.coordinateAlgebraFiniteType C)
  have : Algebra.Smooth k (Lie.coordinateAlgebra C) := {}
  exact smooth_of_coordinateAlgebra_smooth C

/-- The internal formal-to-smooth bridge, uniformly over fields and universes. -/
def SmoothOfFormallySmoothStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G)
    [IsClosedImmersion j.hom.hom.left] [Smooth G.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom],
    Algebra.FormallySmooth k (Lie.coordinateAlgebra C) → Smooth C.X.hom

/-- The coordinate transport and finite-presentation argument prove the bridge. -/
theorem smoothOfFormallySmoothStatement : SmoothOfFormallySmoothStatement.{u} := by
  intro k _ G C j _ _ _ _ h
  exact smooth_of_formallySmooth j h

end Langlands.GroupScheme.Diagonalizable.FixedSubgroupSmoothAlgebraBridge
