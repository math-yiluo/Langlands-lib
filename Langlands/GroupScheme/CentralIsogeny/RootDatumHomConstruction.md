# Actual root-datum morphisms for central isogenies

Authors: Worker 1375 and Worker 1283.

This internal supporting module constructs
`IsCentralIsogeny.rootDatumHomOfCentralIsogeny` on any supplied actual root data.
For a commuting square over a central isogeny of affine locally finite-type
group schemes over an arbitrary field, assume that both tori are split, that
the target torus inclusion is closed, and that the torus restriction is an
isogeny. There is no self-centralizer or ambient Lie-dimension premise in this
construction. The root index types may have independent universes.

The nonzero-weight differential equivalence gives
`roots (i ≫ φ) = roots i`. The torus isogeny is a flat surjection, so its actual
character pullback is injective. The published split-torus weight restriction
formula then gives a bijection from the target roots to the source roots.
`IsRootDatumOf` identifies these supports with the root ranges of the supplied
data, yielding the actual root index equivalence used by
`RootDatumHom.ofRootCoroot`.

For the supplied coroots, the source reflection is realized by an actual
normalizing point, by `IsRootDatumOf`. Its image realizes the target reflection
defined by the pushed-forward source coroot. Both this reflection and the one
from the supplied target coroot lie in the full target Weyl image. The published
`splitTorusWeylImageFinite` proves that this entire image is finite for a closed
split torus in an affine locally finite-type group. The published
`IsRootDatumOf.coroot_comp_of_finite_weylImage` uses finite order of the product
of the two reflections to identify their functionals, and the target perfect
pairing identifies the supplied coroots. This handles the specific supplied
root data, including their central lattice directions.

`RootDatumHom.ofRootCoroot` uses actual character pullback and actual
cocharacter pushforward. Their transpose identity is associativity of
composition in the torus category. The specification proves both displayed
map formulas and both injectivity claims. Character injectivity follows from
the torus restriction being an epimorphism. Cocharacter injectivity follows
from its finiteness, using `cocharacterMapInt_injective_of_isFinite`, which
permits nonsmooth or inseparable finite kernels.

The separate theorem `rootDatumHomOfCentralIsogeny_isIso_iff` retains the
explicit premise that the **full scheme-theoretic** kernel of the original
central isogeny lies in the source torus. Bijectivity of character pullback is
equivalent to invertibility of the split-torus restriction. If the ambient map
is invertible, maximality of the source torus makes its restriction invertible.
Conversely, under the kernel-containment premise, invertibility of the
restriction makes the full ambient map monic on all test schemes. The ambient
finite flat surjection is therefore an isomorphism. No containment assertion is
silently inferred from the root comparison.

Finally, `centralIsogenyRootDatumHom_of_kernel_containment` assembles the exact
published target from a universal family of these full-kernel containments.
For its connected reductive groups the torus restriction is an isogeny by the
published maximality theorem for images of split maximal tori. This universal
containment family remains an explicit, unproved premise of the reduction; this
supporting construction alone does not establish the full host target.

The provenance is internal: the module combines the actual nonzero-weight
coefficient argument, published root support and coroot comparisons, the actual
root-pairing morphism constructor, torus restriction isogeny and lattice
comparisons, and the all-test-scheme kernel criterion. Worker 1283 contributed
the commutator tangent lift underlying the nonzero-weight equivalence. No
smoothness, separability, characteristic, perfection, or algebraic closedness
assumption is added to the full target by this reduction.
