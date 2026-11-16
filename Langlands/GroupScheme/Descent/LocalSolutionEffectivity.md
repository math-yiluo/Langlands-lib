# Effective gluing of supplied local étale solutions

This is an internal construction derived from `LocalSolutionGluing`, actual
transport under restriction (`ReindexTransport`), and reconstruction from an
underlying scheme solution (`SchemeSolutionGroup`). It makes no external
source claim. It is a prerequisite for general-base effectivity and the host
quasi-split inner-form proof.

All schemes lie in an arbitrary universe `u`. Let `p : S → B` be surjective
and étale, `G` an actual group scheme over `S`, and `D` a Čech descent datum
for `G` along `p`. Let `𝒰` be an open cover of `B`, indexed by a small thin
category, with the `LocallyDirected` structure. The input family `s i` is an
actual `Solution (D.baseChange (𝒰.f i))` for each chart. No affineness or
quasi-compactness hypothesis is imposed here. The local solutions are supplied;
this unit does not construct them.

The preceding gluing construction supplies a scheme `obj D 𝒰 s` over `B`,
a map `proj D 𝒰 s` from the original group scheme, its pullback square, and
exact recovery of each local quotient projection. The missing compatibility
is the equality of the images of the two endpoints of the original relation.

`move_proj_of_chart` proves this equality for any transported point whose base
map factors through a specified chart, on every test scheme `Z`. It lifts the
original and new `S` coordinates to `S ×_B U_i` using their shared chart
coordinate, then lifts the original group point to the restricted group. The
local solution identifies this lifted point with its transport under the
restricted datum. `Datum.move_reindex_fst` identifies the original-group
projection of that transported point with its transport under `D`. Exact
local recovery of `proj` on both ends gives the stated equality under the
global projection. All equalities are scheme morphism equalities, including
on nonreduced test schemes.

`relation` pulls the base open cover back to the actual original relation
scheme along its source's map to `B`. On each resulting chart it applies
`move_proj_of_chart` to the original source and the target's `S` coordinate.
`Datum.move_relation` recovers the original target. The open cover's morphism
extensionality then proves exactly

`D.source ≫ proj D 𝒰 s = D.target ≫ proj D 𝒰 s`.

`schemeSolution` packages this relation equation with the previously
constructed actual quotient and its cartesian square. `solution` applies
`SchemeSolution.solution` to reconstruct the actual group operations and the
isomorphism over `S` compatible with the original datum. Thus a global
`Solution D` is constructed from the supplied local solutions. Unconditional
local-solution existence, affine descent, reductive geometry, and the host
inner-form theorem remain separate obligations.
