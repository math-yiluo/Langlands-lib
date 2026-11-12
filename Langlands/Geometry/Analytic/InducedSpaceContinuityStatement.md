# Statement: induced spaces of `H`-spaces are `G`-spaces

Author: Worker 21.

This module states, without proof, that Berkovich's induced space `X_{G/H}`
of an `H`-space `X` is a `G`-space when `H` is an open subgroup of a
topological group `G`. The induced space and its action are constructed in
module `InducedAnalyticSpace`. The module contains one Prop-valued
definition,
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.ContinuityStatement`.

## The statement

`ContinuityStatement : Prop`. Let `K` be a complete ultrametric normed field
in universe `u`. Let `G : Type z` be a group with a topology making it a
topological group (`IsTopologicalGroup G`), and `H` an open subgroup of `G`.
Let `X : Action (LocalizedCategory.{u, max z v, max z v}) H` be an analytic
space with an action of `H` satisfying `gSpaceProperty K H` (module
`ContinuousAnalyticAction`). The group `H` carries the subspace topology.
Then `inducedAction H X` satisfies `gSpaceProperty K G`.

`gSpaceProperty` is the Library's formalization of Berkovich's `G`-spaces
(1996 manuscript, §1.1, printed pp.1–2): the underlying topological space is
Hausdorff, and the action `G → G(X)` is continuous for Berkovich's topology on
the automorphism group, defined by the subgroups `G_ε(X)` for `ε ∈ E(X)`
(`IsContinuousAction`). With this statement, `X_{G/H}` is an object of
`GSpace K G`. Its universal property (`InducedSpace.homEquiv`) then holds in
the full subcategory of `G`-spaces.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2: "Let H be an open subgroup of a topological group G, and
let X be an H-space. Then there is a unique (up to a canonical isomorphism) an
H-morphism f : X → X′ to a G-space X′ such that any H-morphism ϕ : X → Y to a
G-space Y extends in a unique way to a G-morphism ϕ′ : X′ → Y." The construction
that follows takes `X′ = X_{G/H}`, so `X_{G/H}` is a `G`-space. The statement
transcribes this for the Library's construction.

Derived choices: the universes are those of `InducedAnalyticSpace`.
`IsTopologicalGroup G` makes explicit that `G` is a topological group, as in
the source.

## Expected proof route

None of this is formalized here.

- Hausdorff: the underlying space of `X_{G/H}` is the topological sigma type
  of copies of the Hausdorff space of `X` (`sigmaPresentation_space`).
  Disjoint unions of Hausdorff spaces are Hausdorff.
- Continuity: a test triple `(U, f, t)` on `X_{G/H}` has a compact affinoid
  domain `U`, so `U` meets only finitely many copies `c_1, …, c_n`. On the
  open subgroup `⋂ c_i.out H c_i.out⁻¹`, every `g` fixes the cosets `c_i`
  and acts on the copy `c_i` by `κ(g, c_i) = c_i.out⁻¹ g c_i.out ∈ H`.
  Conjugation is continuous, and the action of `H` on `X` is continuous on
  the clopen pieces `U ∩ copy c_i`. Together these give a neighbourhood of
  `1` on which the action is near the identity for `(U, f, t)`.

## Scope

This is a `lean.statement`: nothing is proved here.
