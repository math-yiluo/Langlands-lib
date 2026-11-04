# Actual Lie coordinates and dimensions of split tori

This internal development completes the coordinate description of the actual
dual-number identity kernel of a split torus, then compares dimensions under
an isogeny. It combines the published split-torus unit coordinates, their
infinitesimal linear injection, and the integral cocharacter quasiinverse.

For any commutative base ring `R`, finite index type `I`, and commutative
`R`-algebra `A`, `splitTorus.infinitesimalLinearEquiv` identifies `I → A` with
`Additive (lieKernel (splitTorus (Spec R) I) A)`. Its forward map is the
published `infinitesimalLinear`: the coordinate `v i` gives the unit
`1 + epsilon * v i`. For surjectivity, reduction to the identity says every
coordinate has constant coefficient one. Its epsilon coefficient therefore
recovers the vector. Injectivity and linearity are the published coordinate
lemmas. This uses the actual point functor and epsilon-scaling module action.

The existing `Lie.targetEquiv` from `Rational.CrossTorusLieTransport` transports these Lie kernels along an actual affine
group-scheme isomorphism. Its forward map is `targetMapLinear` and its inverse
is the differential of the inverse group-scheme map. The two identities follow
by postcomposition on dual-number points.

Over any field `k`, the coordinate equivalence shows that Lie dimension is
`Nat.card I`. For an arbitrary split commutative group scheme `T`, transporting
both Lie coordinates and integral cocharacter coordinates through the same
split presentation gives `IsSplitTorus.finrank_lieKernel_eq_cocharacter`:

```
finrank k (Additive (lieKernel T.toGrp k))
  = finrank Z (cocharacterLattice T).
```

An isogeny of split tori has a two-sided nonzero integer quasiinverse by the
published `IsSplitTorus.exists_isogeny_quasiInverse`. Each induced cocharacter
map is injective because its source lattice is torsion free. The lattices are
finitely generated, so the two integral injections give opposite rank bounds.
Their ranks, hence the actual Lie dimensions, are equal. This applies in every
characteristic, including inseparable isogenies.

Finally, `Lie.finrank_zeroWeight_eq_of_torus_isogeny` combines this equality
with `Lie.finrank_zeroWeight_of_selfCentralizing` for both inclusions. It
retains the explicit all-test self-centralizer equalities and monicity of
both inclusions. Proving those geometric equalities for maximal tori remains
a separate obligation. This file does not prove the complete central-isogeny
root-datum theorem.

The provenance is internal: these are coordinate, functoriality, and finite
integral-rank consequences of the named Library constructions. No additional
structure theorem is assumed.
