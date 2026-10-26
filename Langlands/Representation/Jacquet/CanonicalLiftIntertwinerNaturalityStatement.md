# Canonical Jacquet lift naturality under representation intertwiners

`Langlands.Jacquet.CanonicalLiftIntertwinerNaturalityStatement` is a closed
proposition with independent universes for the group `G` and the two complex
representation carriers `V` and `W`. It specifies elementary naturality for the
existing constructions in `CanonicalLiftDefinitions`. This module states the
proposition; it supplies no proof.

The quantified data are an arbitrary topological group, smooth complex
representations `rho` and `sigma`, a compact open subgroup `K`, an arbitrary
element `g`, and an actual representation intertwiner `f : rho -> sigma`.
There is no local-field, admissibility, finite-length, finite-dimensionality,
contraction, or parabolic-shape hypothesis.

## Stable-image preservation

Write `C_rho` for `compressedAction rho hρ K hK g`. This is the operator on the
actual `K`-fixed vectors obtained by applying `rho(g)` and then the normalized
compact average. The stable image is the actual submodule
`intersection_r range(C_rho^r)` for all natural numbers `r`, including zero.
It is not an arbitrarily chosen subspace or an assertion that those ranges
stabilize.

The first conjunct says that `fixedVectorsMap f K.toSubgroup` sends each member
of this stable image into the corresponding stable image for `sigma`. The
representations may have different carrier universes, and `f` need not be
injective, surjective, or an isomorphism.

## The actual quotient square

For every pair of actual subgroups `N` and `M` with `M` normalizing `N`, put
`H = K.toSubgroup.comap M.subtype`, the subgroup `M intersect K` viewed inside
`M`. The codomain of `fixedJacquetMap rho N M hMN K.toSubgroup` is the subspace
of `H`-fixed vectors in the actual coinvariant quotient, with its
**unnormalized** descended `M`-action.

For every `K`-fixed vector `v`, the second clause states the equality of fixed
quotient vectors

```
fixedJacquetMap_sigma(fixedVectorsMap_f(v))
  = fixedVectorsMap_(Jacquet.map_f)(fixedJacquetMap_rho(v)).
```

Here `Jacquet.map N M hMN f` is the published map on the actual quotients.
On a class represented by `v`, it is the class represented by `f(v)`. Thus the
equation concerns the actual quotient presentations, not just their
isomorphism classes.

## Conditional inverse-lift naturality

For the same `N`, `M`, and `hMN`, assume that each existing
`stableImageJacquetMap` for `rho` and `sigma` is bijective. These are the two
explicit local premises `hρbij` and `hσbij` of the final clause; neither is a
premise of the preservation or quotient-square clauses.

Each inverse lift is exactly the inverse of `LinearEquiv.ofBijective` applied
to the respective actual `stableImageJacquetMap`. For every `H`-fixed source
quotient vector `j`, the final equality says

```
f(source inverse lift of j, included into V)
  = target inverse lift of Jacquet.map_f(j), included into W.
```

Both sides are vectors of the actual target representation carrier `W`.
`stableImageToRepresentation` performs the two existing inclusions from the
stable image through fixed vectors into the representation. No new lift or
stable-image map is postulated. The bijectivity proofs are explicit inputs to
the two equivalences; proof irrelevance makes their choice immaterial.

## Internal provenance and scope

This is derived internal linear algebra on already published constructions,
not a translation of a separate literature theorem. The prospective proof uses
`compressedAction_natural` to commute the fixed-vector map with every power by
induction, hence preserve each power range. The quotient equation follows from
`Jacquet.map_mk`. Stable-image preservation and that equation identify the image
of a source lift with the unique target lift, using the assumed bijectivity of
the target restriction.

The statement is distinct from `CanonicalLiftGroupTransportStatement`, which
changes groups through a continuous group equivalence. Here the group remains
fixed and the representations vary by an arbitrary intertwiner. This module
proves no stabilization or quotient bijectivity, makes no assertion of a global
canonical pairing or Jacquet duality, and does not prove the generic
multiplicity comparison or irreducible-head consequence.
