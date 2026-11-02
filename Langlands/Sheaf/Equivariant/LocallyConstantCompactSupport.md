# Compact sections of the full locally constant equivariant sheaf

Author: Worker 13. This internal comparison connects actual global sections of
the full ordinary-open locally constant module sheaf with the previously
constructed compactly supported locally constant function representation.

The space, group, commutative coefficient ring and coefficient module have
independent universes `u`, `v`, `r` and `w`. The group acts on the space and
each point operator is continuous. Coefficients are arbitrary algebraic
module representations at this stage; no topology is imposed on them.
`ordinary` is the actual ordinary-open restriction of the constructed sheaf.
`representation` is its original global-section action restricted to every
section with compact local support.

`restrict_apply` evaluates the original sheaf restriction of the actual
whole-space section identification. Its inverse-label coefficient operator
is the identity on an ordinary inclusion. A zero restriction on a neighborhood
therefore implies a zero function value at the point. Conversely, the zero
fiber of a locally constant function is open; that fiber is an actual
neighborhood where the restriction vanishes. This proves `vanishesNear_iff`
without assuming a support comparison or supplying additional data.

Negating that equivalence proves `support_eq_functionSupport`. Local support
is closed by the already proved restriction argument, so its equality with
the nonzero function support also proves `support_eq_tsupport`. Thus the
compactness condition is exactly the original function compactness condition.
`linearEquiv` restricts the earlier actual whole-space linear equivalence and
its inverse to the full compact submodules. Their linearity and inverse laws
are inherited from that equivalence. Its proved equivariance restricts as
well, giving `equiv` and `repIso` in the algebraic representation category.

The original coefficient intertwiners define `functionFunctor`. Constructing
the full locally constant sheaf and then taking its actual compact sections
defines `sectionsFunctor`. The equivalences are natural under these actual
pointwise coefficient maps, giving `comparison`.

For the smooth constructions the group is a topological group, the spatial
action is jointly continuous, and the coefficient representation is smooth.
The previously proved smoothness theorem applies to every compactly
supported locally constant function: compact support gives an open spatial
stabilizer, and the finite coefficient range permits intersection with all
coefficient stabilizers. Transport through the constructed surjective
intertwiner proves `representation_isSmooth` for the entire compact-section
module. It does not select a smooth-vector submodule. `smoothSections`,
`smoothMap` and `smoothFunctor` bundle these actual sections and actual
coefficient maps in the published smooth representation category.
`smoothComparison` is their natural isomorphism with the existing full
compact-function smooth coefficient functor.

The provenance is internal: this module combines
`Sheaf.Equivariant.LocallyConstant`, `Sheaf.Equivariant.LocalSupport`,
`Representation.LocallyConstant.CompactSupport`, and the published
surjective-intertwiner smoothness transfer. It makes no new original-literature
assertion. The ordinary local support agrees with the actual stalk support
in its supported aligned universes by the imported `LocalSupport` theorem.
This result does not identify ordinary opens with finite rational transport
sites, analytic or etale sites, and does not construct Godement acyclicity,
derived comparisons, arithmetic towers or the Harris specialization.
