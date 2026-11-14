# Actual vector central isogeny for a split type-D group

Work over any field `k : Type u`, in every characteristic. Let `G` be an affine
connected reductive group with a supplied split maximal torus `i : T → G`, and
let `P` be a finite reduced root datum of that actual torus. Assume the integral
coroot span is the full cocharacter lattice. Supply a base `B`, an integer
`n ≥ 4`, and a numbering `e : B.support ≃ Fin n` preserving every entry of
`CartanMatrix.D n`.

`VectorCentralIsogeny P B hspan hn e i` packages an actual morphism
`p : G → identityComponent (OrthogonalMatrix.groupScheme (Fin n) k)`, a map
from `T` to the standard split torus, a proof that `p` is a central isogeny,
and a commuting square with the supplied torus inclusions. Its
`characterImage` field identifies the full integral range of actual character
pullback with

`P.rootSpan ℤ ⊔ span ℤ {fundamentalWeightBasis P B hspan (e.symm 0)}`.

The structure itself only records these data and properties; the construction
`vectorCentralIsogeny` supplies an inhabitant under the hypotheses above. It
applies [VectorRootDatumMap](VectorRootDatumMap.md) to obtain an actual
orthogonal root datum and an injective morphism on both lattices. The published
[split central Isogeny Theorem](../Reductive/SplitCentralIsogeny.md) realizes
that morphism as maps of the groups and tori. Extensionality identifies its
weight map with `characterLattice.comapHom` of the actual torus map, so the
integral range calculation transfers unchanged.

`VectorCentralIsogeny.character_kills_kernel` proves that every character in
that image kills the kernel on `T`, on every `k`-scheme of test points. The
closed immersion of the target torus permits cancellation to show that such a
point is killed by the torus map; evaluating a pulled-back character then gives
the identity. `fundamentalWeight_kills_kernel` specializes this result to the
weight at numbered vertex zero, using its membership in the stated range.
These arguments retain nonreduced test schemes and impose no restriction on
characteristic, on the universe, or excluding `D₄`.

This is an internal derivation from the named Library results, not an appeal
to a classification of spin presentations. It supplies a split geometric
isogeny and its kernel alignment. Galois descent and the parent aligned
spin-cover theorem remain separate obligations.
