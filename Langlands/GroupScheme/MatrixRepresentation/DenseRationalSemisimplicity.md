# Semisimplicity detected on a dense rational-point family

This internal comparison module uses the namespace
`Langlands.GroupScheme.MatrixRepresentation`.

Let `k : Type u` be a field and `J` a group scheme over `k`. A matrix
representation `ρ : MatrixRepresentation J n` has a finite coordinate type
`n : Type` with decidable equality. The predicate `IsSemisimpleOnTests ρ`
means that the supremum of all subspaces `W` satisfying the following
three conditions is the whole coordinate space:

- `ρ.IsStableSubspace W`, using the published predicate that tests all
  commutative `k`-algebras and all `k`-linear coefficient functionals;
- `W ≠ ⊥`;
- every all-test stable subspace `U ≤ W` is either `⊥` or `W`.

This is exactly the sum-of-simple-subspaces predicate in the published
`CharZeroSemisimpleRepresentationIdentityComponentStatement`. Defining it
here introduces no characteristic or finite-type premise.

## Detection by a dense family

For the two detection theorems, assume that `J` is reduced and affine over
`k`. Let `I : Type v` be a monoid in a universe independent of `u`, and let
`α : I →* PointTopology.RationalPoint k J.X` have dense image on underlying
scheme points, in the precise sense of the published
`HasDenseRationalPointFamily`.

`isStableSubspace_iff_denseRationalAction` proves that a subspace is
all-test stable if and only if it is stable under the abstract monoid
representation `ρ.rationalAction.comp α`. The forward direction applies
the published `IsStableSubspace.rationalMatrix_mulVec_mem`. The reverse
direction is the published `isStableSubspace_of_denseRationalFamily`.
That result uses reducedness and scheme-point density to detect the
vanishing of the coordinate stability defect.

`isSemisimpleOnTests_iff_denseRationalAction` proves

```text
ρ.IsSemisimpleOnTests ↔
  Representation.IsSemisimpleRepresentation (ρ.rationalAction.comp α).
```

The proof rewrites the right-hand side with
`RepresentationSemisimpleTransport.isSemisimple_iff_sSup_simples` and
replaces every occurrence of stability by the preceding equivalence.
This compares exactly the same subspaces and inclusion order, so both
simplicity and their supremum agree. The result requires neither an
algebraically closed field, a characteristic assumption, nor a
finite-type assumption. It includes empty coordinate types.

## Tensor evaluation

The remaining theorems require only a field and a group scheme. For every
rational point `g`, `rationalAction_toMatrix` identifies the ordinary
matrix of `ρ.rationalAction g` with `ρ.rationalMatrix g`, using the inverse
relationship between `LinearMap.toMatrix'` and `Matrix.toLin'`.

For two matrix representations `ρ` and `σ` of the same group scheme,
`rationalAction_tensor` identifies the rational-point action of the
actual tensor scheme representation with
`CoordinateTensor.representation ρ.rationalAction σ.rationalAction`.
The proof compares the linear maps on every vector. The published
coordinate tensor matrix theorem reduces this to a matrix equality:
each tensor coefficient is the product of the two original coefficients,
by `tensor_pointMatrix_entry`, and passage from global sections of
`Spec k` to `k` preserves multiplication.

`rationalAction_tensor_comp` restricts this equality along any monoid
family `α`. Density, affine structure, reducedness and finite type are
unnecessary for the tensor identities.

## Provenance and scope

This is internal content derived from the published matrix
representations, dense rational stability detector, tensor matrix
formulas, coordinate tensor representation, and the internal
semisimplicity transport module. The comparison is a direct reuse of
those Lean declarations; no additional correspondence with external
literature is claimed. This module proves no characteristic-zero tensor
semisimplicity theorem.
