# Full locally constant module sheaves on a moving space

Author: Worker 13. This is an internal ordinary-topological construction from
the published labelled-open category and Mathlib's sheaf of functions satisfying
a local predicate.

The inputs are a group `G` acting on a topological space `X`, continuity of
each individual point operator, an arbitrary commutative ring `R`, and an
algebraic representation on a module `M`. The space, group, ring and module
have independent universes `u`, `v`, `r` and `w`. Function modules have carrier
universe `max u w`. No coefficient topology, joint action continuity, compactness,
smoothness or nonemptiness is assumed.

`pointMap` is the continuous map on the actual open subspaces specified by
the original arrow label. `pullback` precomposes with this point map and applies
the inverse coefficient operator. `presheaf` uses every locally constant
function on every open, and these actual linear pullbacks. The representation
and point-action laws prove its identity and composition laws.

`localPredicate` states local constancy of a function. To prove its locality,
the implementation temporarily equips the coefficient set with the discrete
topology and uses Mathlib's local continuity predicate. This topology is local
to the proof. `underlyingIso` identifies the forgotten ordinary presheaf with
the full subpresheaf of functions satisfying this predicate; the label-one
coefficient operator is the identity. Mathlib's local-predicate sheaf theorem
therefore gives `forget_isSheaf` for arbitrary open covers. Reflection of the
actual matching limits gives `isSheaf` in modules. The reflection proof uses
the smallness of the set of sections supplied by the given limiting cone,
constructs the module limit and reflects its isomorphism. It does not require
all limits of arbitrary size to exist in the module category.

`sheaf` packages this result in the existing category of moving-space
equivariant sheaves. Coefficient intertwiners act pointwise on every section.
Their original intertwining equations prove naturality for all labelled
arrows, giving `map` and `functor`.

`globalSectionsLinearEquiv` identifies locally constant functions on `X`
with sections over the largest open, by restriction and inverse restriction
along its actual whole-space parametrization. Its maps are linear and
inverse by evaluation. `globalRepresentation` is the already constructed
global-section action, converted to a module representation. Its explicit
formula is `ρ g (s (g⁻¹ • x))`. This proves equivariance of the section
identification and constructs `globalSectionsRepIso` with the previously
published diagonal locally constant function representation.

The construction reuses `Langlands.Sheaf.Equivariant.Topological`,
`Langlands.Representation.LocallyConstant.CompactAction`, and pinned Mathlib's
local predicates, locally constant linear maps and module limits. It adds no
new original-literature assertion. The module-valued finite rational transport
sheaf in `OpenSubgroupLocallyConstantSheaf` uses a different site and is not
identified with this ordinary-open sheaf. Germ-support and compact-support
comparison, smoothness of compact sections, analytic or etale site comparison,
Godement resolutions, cohomology and Harris specialization remain separate
obligations.
