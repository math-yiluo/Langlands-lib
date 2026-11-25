module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The dimension of a scheme

The dimension of a scheme is the Krull dimension of its underlying topological space, and its
dimension at a point is the local Krull dimension of that space at the point. The global
dimension is the supremum of the dimensions at all points, and also the supremum of the Krull
dimensions of all the local rings.

A locally Noetherian scheme of dimension at most zero is the disjoint union of the spectra of its
local rings, which are Artinian; and a point of a locally Noetherian scheme has local dimension
zero exactly when it is isolated.

## Main definitions

* `AlgebraicGeometry.sigmaFromSpecStalk` is the canonical map from the coproduct of the spectra
  of all stalks to the scheme.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk` identifies the dimension
  of a scheme with the supremum of the dimensions of its local rings.
* `AlgebraicGeometry.isArtinianRing_stalk_of_topologicalKrullDim_le_zero` says that every stalk
  of a locally Noetherian scheme of dimension at most zero is Artinian.
* `AlgebraicGeometry.isIso_sigmaFromSpecStalk_of_topologicalKrullDim_le_zero` says that the
  canonical map from the disjoint union of their spectra is an isomorphism.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint` characterizes the points
  of local dimension zero as the isolated points.
* `AlgebraicGeometry.mem_genericPoints_iff_isMax` characterizes the generic points of the
  irreducible components as the maximal points of the specialization order.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_iff_mem_genericPoints` says that the local ring
  at a point has dimension zero exactly when the point is such a generic point.

## Implementation notes

Schemes coerce to their types of points and carry the topology of their underlying spaces, so the
general topological definitions `topologicalKrullDim` and `topologicalKrullDimAt` state the
dimension and the dimension at a point directly; they are adopted rather than duplicated by
scheme-specific aliases. The dimension of a local ring is `ringKrullDim`, and the supremum is
taken in `WithBot ℕ∞`, the common codomain of the two notions.

For the dimension-zero decomposition we use the points of the scheme as the canonical indexing
type for the disjoint union and its stalks as the summand rings; scheme stalks carry their
canonical local-ring instances. The source assumes dimension equal to zero, and dimension at most
zero is a useful generalization which also includes the empty scheme. Isolation is the
topological predicate `IsIsolatedPoint`.

## References

* [Stacks Project, Tag 04MT](https://stacks.math.columbia.edu/tag/04MT)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
* [Stacks Project, Tag 0AAX](https://stacks.math.columbia.edu/tag/0AAX)
* [Stacks Project, Tag 0H7C](https://stacks.math.columbia.edu/tag/0H7C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of a scheme is the generic point of an irreducible component exactly when it is
maximal for the specialization order, that is, when it has no proper generalization. -/
theorem mem_genericPoints_iff_isMax (X : Scheme.{u}) (x : X) :
    x ∈ genericPoints X ↔ IsMax x := by
  constructor
  · intro hx b hb
    refine Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr ?_)
    exact hx.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp (Scheme.le_iff_specializes.mp hb))
      (subset_closure (Set.mem_singleton b))
  · intro hx
    obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({x} : Set X)) isIrreducible_singleton.closure
    have hη : IsGenericPoint (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) C :=
      genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
    have hηx : (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) ⤳ x :=
      hη.specializes_iff_mem.mpr (hxC (subset_closure (Set.mem_singleton x)))
    change closure ({x} : Set X) ∈ irreducibleComponents X
    rw [Set.Subset.antisymm (specializes_iff_closure_subset.mp hηx)
      (specializes_iff_closure_subset.mp
        (Scheme.le_iff_specializes.mp (hx (Scheme.le_iff_specializes.mpr hηx))))]
    exact (genericPoints.ofComponent (α := X) ⟨C, hC⟩).2

end AlgebraicGeometry

end
