# Smoothness of Renard's original equivariant projector sheaf

This internally derived construction supports Renard III.3.1–III.3.2, printed pp.83–84 /
PDF pp.89–90, on the original inverse sheaf construction of II.2.5, printed
pp.39–40 / PDF pp.45–46. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations have prefix
`Langlands.Sheaf.Renard.SmoothProjectorActionSheaf`. The local proof is an
implementation of the smooth reconstruction needed by III.3; it is not a
separately printed source argument. It uses the original II.2.5 compact-open
section formula and the published local-smoothness infrastructure.

The source is an original compatible nondegenerate pointwise test module
with a smooth representation on its whole carrier. The reconstructed action
sheaf is precisely `ProjectorActionSheaf.sheaf`. Spaces, coefficients and
module carriers are universe zero; the group universe is independent.

Original-vector sections are the published `ProjectorVectorSheaf.originalFamily`:
the component at compact open `W` is `chi_W • m`. Their pullback formula is
proved from the given compatibility law and translated characteristic tests.
The global version intertwines the original module action with the constructed
global section action. Restriction retains the same original vector.

Every section over an actual open, restricted to a compact open `W`, is the
original-vector section of its own component at `W`. This is the published
family compatibility equation, not an assumed surjectivity result for compact
global sections.

For a point of an original local section, choose such a compact open. The
original vector is fixed by an open subgroup because the entire module
representation is smooth. Its original-vector global section is fixed by that
same subgroup. The existing `isLocallyFixedAt_of_globalFixed` and stable
neighbourhoods provide local fixedness. Its restriction agrees with the
original section near the point, so local fixedness transfers to that section.
This proves `isSmoothSheaf` under the explicit `HasStableNeighbourhoods G X`
condition without assuming either sheaf/module comparison
is invertible.

For a jointly continuous action of a topological group, with explicit
`IsLocallyProfinite` predicates on the group and space, the published stable
neighbourhood result supplies the required condition. The published
local-to-compact smoothness theorem gives smoothness of all original compact
sections. `smoothFunctor` lifts the actual reconstruction functor on all
objects and maps; `smoothFunctorToActionIso` retains the original underlying
action-sheaf functor. `isSmoothAction` records this implication with explicit locally profinite
group and space hypotheses. No smooth-vector replacement is made. The
full-subcategory lift changes only smoothness proofs: every underlying
object and original sheaf morphism is the one from `ProjectorActionSheaf.functor`.

The sheaf/module equivalence and invertibility of its canonical comparisons,
induction, coinvariants and the homogeneous-space theorem remain separate.
