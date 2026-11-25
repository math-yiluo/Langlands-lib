# The infinite-place permutation lattice in real coordinates

Let `E : Type v` be a number field. The real coordinate space
`V = InfinitePlace E → ℝ` is the same ambient space used by
`fullLogEmbedding` and `augmentedFullLogUnitLattice`. This module realizes
the published canonical infinite-place permutation module inside `V` as
the full integer coordinate lattice. Its field of definition
`F : Type u` has an independent universe and needs only a field structure
and an algebra structure on `E`.

## The embedded lattice

`infinitePlaceCoordinateLattice E` is the integer span of the standard
real basis `Pi.basisFun ℝ (InfinitePlace E)`. Mathlib's basis-span lattice
instances give its inherited topology the instance `DiscreteTopology`
and give it `IsZLattice ℝ`. The theorem
`infinitePlaceCoordinateLattice_span` exposes its full real span.

`mem_infinitePlaceCoordinateLattice_iff` characterizes its elements as
exactly those real functions whose coordinates are all integer casts:

\[
x\in N\quad\Longleftrightarrow\quad
\forall w\;\exists z\in\mathbf Z,\ z=x(w).
\]

The proof applies `Basis.mem_span_iff_repr_mem` to the standard basis,
whose coordinate function is evaluation. Thus the definition is an
actual discrete full submodule of the required real space.

## Integer coordinates and the canonical representation

`infinitePlaceCoordinateIntegerEquiv E` identifies the embedded lattice
with `InfinitePlace E → ℤ`. It is the composition of the coordinate
representation of the restricted integer basis and the finite-support
to function equivalence. Its formula is

\[
\bigl(\operatorname{infinitePlaceCoordinateIntegerEquiv}(x)(w):
\mathbf R\bigr)=x(w).
\]

`infinitePlaceCoordinateIntegerEquiv_cast` proves this from
`Basis.restrictScalars_repr_apply`; the inverse formula
`infinitePlaceCoordinateIntegerEquiv_symm_apply` follows by applying the
forward identity to an inverse image.

`infinitePlaceLatticeRealization F E` is the integer linear equivalence
from the carrier of the existing `infinitePlaceLatticeRepresentation F E`
to `infinitePlaceCoordinateLattice E`. It first applies the published
`infinitePlaceLatticeFunctionEquiv`, restricted to integer scalars,
then lowers the lifted integer at every place using `ULift.moduleEquiv`,
and finally applies the inverse integer-coordinate equivalence above.
Its exact underlying real-coordinate formula is

\[
\operatorname{infinitePlaceLatticeRealization}(x)(w)
  = (x.\mathrm{coeff}(w).\mathrm{down}:\mathbf R).
\]

`infinitePlaceLatticeRealization_apply` obtains this formula by unfolding
the composition and using the inverse-coordinate identity. This
construction retains the canonical `Rep.ofMulAction` permutation module
and supplies its explicit realization in the real coordinate space.

## Arithmetic action

The acting group is the actual group `E ≃ₐ[F] E` of field automorphisms.
`infinitePlaceCoordinateLattice_invariant` proves stability under
`fullLogPermutation F E`, which acts by
`(g x)(w) = x(g⁻¹ • w)`. The membership characterization makes the proof
a direct evaluation at the permuted place.

`infinitePlaceCoordinateLatticeAut F E` restricts this real permutation
action to an integer linear automorphism homomorphism on `N`. Its inverse
uses `g⁻¹`; all inverse and homomorphism laws descend from the real
action. The theorem `infinitePlaceCoordinateLatticeAut_apply` identifies
the underlying real vector with that action.

Finally, `infinitePlaceLatticeRealization_equivariant` proves

\[
R(\rho(g)x)=\operatorname{infinitePlaceCoordinateLatticeAut}(g)(R(x)).
\]

After subtype and function extensionality, the proof uses the real
coordinate formula, the published inverse-precomposition formula for
canonical representation coefficients, and the coordinate formula in
reverse. No cyclicity or Galois hypothesis is required for these
constructions; number fields with one infinite place are included.

## Provenance and scope

Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof
of Proposition 3.1, printed p.209 (PDF p.218), sets
`V = Hom(T, ℝ)` and `N = Hom(T, ℤ)`, with inverse-precomposition action.
Here `T` is all infinite places, and the source's `N` is realized as a
submodule of `V`. Registered source: `milne-2020-class-field-theory`,
SHA256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

The basis-span construction, explicit integer linear equivalences,
and action restriction are derived adapters of that source construction
using Mathlib's lattice machinery and the already published canonical
permutation representation. This module supplies the second full
invariant lattice in the same real space as the augmented unit lattice.
It asserts no lattice-comparison theorem, cohomology isomorphism, or
Herbrand-quotient formula.
