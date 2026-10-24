# Representation comparisons for the two full real-coordinate lattices

Let `E : Type v` be a number field and `F : Type u` a field, with an
`F`-algebra structure on `E`. The universes are independent. Put
`G = E ≃ₐ[F] E` and `k = NormalizedTwoCocycle.CoefficientScalars.{v}`,
the published lifted integers. No Galois or cyclicity hypothesis is used.

The imported modules provide two full invariant integer lattices in
`V = InfinitePlace E → ℝ`: the augmented unit lattice
`M = augmentedFullLogUnitLattice E` and the coordinate lattice
`N = infinitePlaceCoordinateLattice E`. Write
`M₀ = fullLogUnitLattice E` for the actual logarithmic unit lattice in
the sum-zero hyperplane. This module packages the already proved actions
and equivalences as representations and cohomology isomorphisms.

## The two full-lattice representations

`augmentedFullLogUnitLatticeRepresentation F E` is a representation in
`Rep.{v} k G` with carrier `M`. Its action is exactly
`augmentedFullLogUnitLatticeAut F E g`. Likewise,
`infinitePlaceCoordinateLatticeRepresentation F E` has carrier `N` and
action `infinitePlaceCoordinateLatticeAut F E g`.

Both actions restrict the same real arithmetic permutation action
`(g • f)(w) = f(g⁻¹ • w)`. The integer linear maps are viewed as linear
over `k` by restriction of scalars. Their identity and composition laws
follow from the existing automorphism homomorphisms. The displayed
`_apply` theorems identify the representation actions with these
restricted arithmetic automorphisms on every vector.

## Canonical coordinate realization

`infinitePlaceLatticeRealizationIso F E` is an isomorphism

```text
infinitePlaceLatticeRepresentation F E
  ≅ infinitePlaceCoordinateLatticeRepresentation F E.
```

The source is the existing canonical integer permutation representation
on infinite places. The underlying map is precisely the previously
constructed `infinitePlaceLatticeRealization F E`, now viewed as linear
over `k`. For a vector `x` and infinite place `w`, its real coordinate is
`((x.coeff w).down : ℝ)`, by the imported realization formula.

`Rep.mkIso` packages this linear equivalence with the imported
`infinitePlaceLatticeRealization_equivariant` equation. Thus the
isomorphism relates the original canonical representation to its actual
embedded coordinate lattice; it does not replace either arithmetic
action by a transported action.

## Integral splitting as representations

`fullLogUnitLatticeWithConstantsRepresentation F E` has carrier
`M₀ × k`. It is `Representation.prod` of the existing unit-lattice
representation and the trivial representation on `k`. Its action is

```text
(g, (y,z)) ↦ (fullLogUnitLatticeAut F E g y, z).
```

`fullLogIntegralSplitLifted E` is a `k`-linear equivalence from `M` to
`M₀ × k`. It first applies `fullLogIntegralSplit E`, then leaves the
unit-lattice coordinate unchanged and lifts the integer coordinate:

```text
x ↦ ((fullLogIntegralSplit E x).1,
      ULift.up (fullLogIntegralSplit E x).2).
```

The inverse first lowers the lifted integer and then applies the
inverse integral splitting. Thus on underlying real coordinates it
sends `(y,z)` to `y + fullLogConstant E (z.down : ℝ)`, as follows
from the imported inverse formula. The linear equivalence is formed
over ordinary integers and then restricted to the lifted integer
scalars; no real scalar is substituted for its integer component.

`fullLogIntegralSplitRepresentationIso F E` identifies the augmented
lattice representation with this product representation. The proof of
the intertwining equation reduces to
`fullLogIntegralSplit_equivariant`: its first coordinate is equivariant,
and its second coordinate is unchanged. The underlying-map theorem
states that this categorical isomorphism applies exactly
`fullLogIntegralSplitLifted E`.

## Ordinary cohomology comparisons

For every `n : ℕ`, including zero,
`infinitePlaceLatticeRealizationCohomologyIso F E n` identifies the
ordinary group cohomology of the canonical permutation representation
with that of its coordinate-lattice representation.
`fullLogIntegralSplitCohomologyIso F E n` identifies the cohomology of
the augmented lattice with that of the product representation above.

Both are obtained by applying `groupCohomology.functor k G n` to the
corresponding representation isomorphism. These are actual module
isomorphisms, with no finiteness assumption on the cohomology groups.
The product representation still appears as one coefficient object;
this module does not further split its cohomology into two factors.

## Provenance and limits

Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof of
Proposition 3.1, printed p.209 (PDF page 218), places
`N = Hom(T,ℤ)` and `M = M₀ + ℤe` inside `V = Hom(T,ℝ)`, with the
inverse-precomposition action and fixed constant vector `e`. Here
`T` is all infinite places, and `M₀` is the actual ordinary-unit
logarithm image, using the full multiplicity-weighted logarithm
constructed in the imported modules.

The categorical packaging, lifted-integer coordinate and functorial
cohomology isomorphisms are derived adapters of those constructions.
Their proofs use only the established coordinate realization, integral
splitting and arithmetic equivariance. This contribution does not
identify `M` with `N`, prove equality of their Herbrand quotients,
assert cohomology finiteness, or prove the parent idele-class theorem.
The comparison of the two full lattices and the cohomological product
calculation remain separate obligations.
