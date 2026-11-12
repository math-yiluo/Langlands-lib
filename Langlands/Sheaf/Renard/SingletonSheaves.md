# Singleton sheaf functors and original comparison maps

Worker 151, Task 5297. Source construction for Renard III.3.2, printed p.84 /
PDF p.90, the singleton example in the first paragraph and the displayed Γ_c
functor immediately following it. Source:
`renard-2026-representations-groupes-reductifs-padiques`, French edition dated
9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations have prefix
`Langlands.Sheaf.Renard.SectionActions.SingletonSheaves`.
The group has an arbitrary universe and an arbitrary topology. Its singleton
action is Mathlib's original `PUnit.mulAction`. The singleton and vector
carriers have universe zero; coefficients are actual ℂ. The singleton action
is jointly continuous because its action map is constant. Every singleton
open is stable under the top open subgroup, which supplies
`singletonStableNeighbourhoods`. No topological-group, local-profinite or
countability assumption is required for these constructions. Renard's t.d.
setting is included; his countability hypothesis belongs to the later
transitive-space identification.

`algebraic` is exactly the published full locally constant coefficient-sheaf
functor, specialized to PUnit. Thus a representation on M gives the original
sheaf of all locally constant maps U→M on every open U, with the published
inverse-coefficient transport on labelled arrows. `functor` lifts that same
object and all its original coefficient maps from smooth representations to
Renard's `SmoothActionSheaf G PUnit`. Its compact-section smoothness follows
from the existing local smoothness of the full coefficient sheaf and the
existing implication from local smoothness to smoothness of all compact
sections. The other functor is the published `SectionActions.gammaC`.

`topArrow U y`, for y in U, is the original label-one arrow from the whole
singleton to U. The point y ensures that U contains every point.
`compactFromLocal F U y` applies the original F restriction on that arrow.
Its output is compactly supported since every subset of PUnit is finite.
`toCoefficientSection` assigns to an original local section s the function
y↦compactFromLocal F U y s. This function is locally constant because its
domain is discrete. Empty opens have no y and hence present no special
choice of a section.

`unitComponent` is the resulting sheaf map from F to the coefficient sheaf
of its original compact-section representation. On a labelled arrow, the
naturality square reduces to equality of the two original arrows from the
whole singleton, using their common group label. The inverse coefficient
operator agrees with the original section action because the latter uses
an inverse-labelled section arrow. `unit` is this comparison natural in all
smooth action sheaves: naturality on original sheaf maps follows from their
original restriction squares.

`evaluation` evaluates an actual compact global coefficient section at
PUnit.unit. It is ℂ-linear and intertwines the original section action with
the original coefficient representation. The inverse labels cancel in this
formula. `counit` bundles these evaluations as a natural transformation from
`functor G ⋙ gammaC G PUnit` to the identity on smooth representations.
`unit_apply` and `counit_apply` record these literal local-section and
evaluation formulas.

The names unit and counit identify canonical comparison transformations;
this unit neither assumes nor asserts their invertibility, triangle laws,
an adjunction or the singleton equivalence. The later singleton statement
can assert that these two concrete transformations are isomorphisms and that
the actual functors yield the source's equivalence. Comparison of singleton
global sections with original stalks and its application to the general
point-restriction functor also remain separate.
