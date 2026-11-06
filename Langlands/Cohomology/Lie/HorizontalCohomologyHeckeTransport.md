# Integrated Hecke maps on the original horizontal cohomology

This internal construction combines `Horizontal.mapCohomologyIntertwiner` with
`Hecke.heckeActionIntertwiner`. It uses the existing horizontal complex of
alternating cochains, its differential kernels, and its quotient by boundaries.
The Lie algebra and coefficient modules may have independent universes. The
coefficient group acts compatibly with the Lie brackets; the displayed insertion
identities make the horizontal differential available. A separate topological
group `P` acts smoothly in every degree and commutes with the differential.
Both coefficient complexes use the same Haar measure on `P`.

`mapCohomologyHeckeIntertwiner` takes a family of group intertwiners on horizontal
cochains that commutes with the differentials. It returns an
`Algebra.LinearIntertwiner` between the two existing `cohomologyHeckeAction`s.
It first restricts the cochain map to cycles, descends that map through the
existing quotient, and then integrates its group equivariance.

`mapCohomologyHeckeIntertwiner_toLinearMap` states that this integration retains
the original quotient linear map. `mapCohomologyHeckeIntertwiner_class` states
that a cycle class maps to the class of its transported cycle. Both are
reflexive equalities of the implemented constructions.

`mapCohomologyHeckeIntertwiner_id_of_eq` takes a cochain family equal in each
degree to the identity. It proves that its integrated quotient map is the
identity. `mapCohomologyHeckeIntertwiner_comp_of_eq` takes first, second, and
combined cochain maps and a degreewise equality of the combined map with the
second after the first. It proves the corresponding composition equality of
integrated quotient maps. Each proof first applies the existing cochain-to-
quotient identity or composition lemma, then the generic integrated-intertwiner
equality helper. All three cochain families must satisfy their displayed chain
compatibility conditions; all three actions must be smooth.

The two laws are abbreviations of proved equality terms. They keep their inferred
types to specialize the original quotient without expanding it again during
elaboration. There is no new quotient, comparison isomorphism, spectral or
geometric realization, or automorphic existence assertion. The explicit
insertion, action, chain, and smoothness premises remain part of this generic
interface; an application must discharge them for its actual complex.
