# Splitting from injective rational root restriction

This internal derived unit combines actual rational root restriction with
semisimple character rigidity and finite Galois descent. All fields and group
schemes lie in an arbitrary universe `u`; no characteristic is excluded.

Let `G` be an affine, locally finite type, quasi-split semisimple group over a
field `k`. Let `a : S → G` be a maximal split torus and `j : T → G` a maximal
torus. Supply `f : S → T` whose composition with `j` is `a`, and a finite
Galois extension `L/k` over which `T` is split.

`IsQuasiSplit.isSplitTorus_of_rationalRootRestriction_injective` assumes that
the actual linear map `rationalRootRestriction` on the rational root spans
is injective. The preceding root-restriction module proves that this forces
every actual root character over `L` to be fixed by every `k`-automorphism of
`L`. Semisimplicity ascends to `L` by the published algebraic-extension
ascent theorem. The published maximal-torus base-change theorem gives
maximality of `j_L`. The fixed-root splitting theorem then proves that `T`
is already split over `k`.

`torusFactorIsoOfRationalRootRestriction` constructs a group-scheme
isomorphism `S.toGrp ≅ T.toGrp`. Once `T` is split, maximality of the original
split torus `a` implies that the supplied factor `f` is an isomorphism.
The constructed isomorphism has homomorphism exactly
`CommGroupScheme.groupHom f`, as stated by its `_hom` theorem. Transporting
maximality of `j` through this isomorphism gives
`isMaximalTorus_of_rationalRootRestriction_injective` for the original map
`a`.

The two `_of_rootSystems` consequences supply the injectivity premise from
explicit rational root pairings `P` on the target root span and `Q` on the
source root span, each paired with its rational dual. Both must be root
systems, `Q` must be irreducible, and their entire root images must be
exactly the rationalized actual roots of `a` and `j_L`, respectively. The
full indexed pairing of `P` must be symmetric. The index types may lie in
independent universes. The rational-restriction injectivity theorem applies
to precisely these data. The consequences assert splitting of `T` and
maximality of the original `a`, respectively.

Finally, `isMaximalTorus_of_hasReducedSimplyLacedRelativeRootSystem`
unpacks the published full-root predicate
`HasReducedSimplyLacedRelativeRootSystem a` to obtain `P`, its exact root
image and its symmetric pairing. The supplied source root system `Q`, its
irreducibility and its exact actual-root image remain hypotheses. The
reducedness, crystallographicity and evaluation-pairing clauses of the
target predicate are stronger than this argument needs.

This module does not assert existence or irreducibility of `Q`, choose a
containing maximal torus or splitting extension, or prove the unrestricted
`QuasiSplitSimplyLacedSplittingStatement`. It does not supply a stable
chamber or the host local anisotropic affine-diagram theorem. Its provenance
is the composition of the cited Library and preceding internal
constructions, with each unresolved root-system input retained explicitly.
