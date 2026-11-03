import Langlands.GroupScheme.Torus.FiniteCoordinateWeightDecomposition
import Langlands.GroupScheme.Lie.FiniteCoordinateScalarExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Homogeneous bases of actual split-torus Lie actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A finite basis of the actual Lie kernel, each vector belonging to one
all-test differential character weight space. -/
structure HomogeneousLieBasis (b : AutomorphicAction H G) (j : T.toGrp ⟶ H) where
  dimension : ℕ
  basis : Module.Basis (Fin dimension) k (Additive (lieKernel G k))
  weight : Fin dimension → characterLattice T
  mem_weight : ∀ i, basis i ∈ b.lieWeightSpace j (weight i)

namespace Lie.FiniteCoordinates

/-- A natural finite-coordinate Lie module has a homogeneous finite basis for
any action of a split torus. -/
def homogeneousBasis {d : ℕ} (c : Lie.FiniteCoordinates G d)
    (hT : IsSplitTorus T.toGrp) (b : AutomorphicAction H G) (j : T.toGrp ⟶ H) :
    HomogeneousLieBasis b j := by
  classical
  let e := c.equiv (CommAlgCat.of (CommRingCat.of k) k)
  letI : FiniteDimensional k (Additive (lieKernel G k)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let v := fun χ : characterLattice T => Module.finBasis k (b.lieWeightSpace j χ)
  let h := b.isInternal_lieWeightSpace_of_finiteCoordinates k G c T hT j
  let w := h.collectedBasis v
  letI := FiniteDimensional.fintypeBasisIndex w
  let q := Fintype.equivFin (Σ χ : characterLattice T,
    Fin (Module.finrank k (b.lieWeightSpace j χ)))
  exact {
    dimension := Fintype.card (Σ χ : characterLattice T,
      Fin (Module.finrank k (b.lieWeightSpace j χ)))
    basis := w.reindex q
    weight := fun i => (q.symm i).1
    mem_weight := fun i => by
      rw [Module.Basis.reindex_apply]
      exact h.collectedBasis_mem v (q.symm i) }

end Lie.FiniteCoordinates

namespace HomogeneousLieBasis

variable {b : AutomorphicAction H G} {j : T.toGrp ⟶ H}
    (q : HomogeneousLieBasis b j) {d : ℕ} (c : Lie.FiniteCoordinates G d)

/-- The extended basis retains its all-test character eigenvector equations. -/
theorem differential_basis (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : Lie.AffinePoints T.toGrp A) (i : Fin q.dimension) :
    b.differential (t ≫ j.hom.hom) (c.baseChangeBasis q.basis A i) =
      (Lie.characterValue (q.weight i) t : A) • c.baseChangeBasis q.basis A i := by
  rw [c.baseChangeBasis_apply]
  exact q.mem_weight i A t

end HomogeneousLieBasis
end Langlands.GroupScheme
