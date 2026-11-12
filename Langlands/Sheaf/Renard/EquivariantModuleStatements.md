# Renard III.3: actual equivariant sheaves and compatible test modules

These are unproved closed proposition targets for David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.1 Definition, printed p.83 / PDF p.89, the identification
of sheaves with an action and nondegenerate `D(X)`-modules with a compatible
linear action. The smooth restriction uses the following smoothness sentence
and the category definition in III.3.2, printed p.84 / PDF p.90. Registered
source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original pages were read directly. Renard invokes the II.2.5 equivalence;
these targets express the equivariant correspondence on the actual published
complex-linear functors.

All declarations are in
`Langlands.Sheaf.Renard.EquivariantModuleStatements`.

`AlgebraicStatement` quantifies over an actual topological group
`G : Type uG`, a jointly continuous action on `X : Type`, and explicit
`IsLocallyProfinite` predicates on both. The Hausdorff compact-open bases
and actual supplied topologies and actions are retained. The group universe
is independent of the original universe-zero complex coefficients, section
and module carriers. The group locally profinite premise is retained even
though the two construction functors themselves have weaker sufficient
hypotheses. No smoothness or finite-dimensionality is assumed.

The required category equivalence has forward functor exactly
`CompactSectionActions.functor hX` and inverse exactly
`ProjectorActionSheaf.functor hX`. The first uses all original compact
sections with the published test action and the original group operators,
linear for the canonical complex structure. The second uses the original
projector-family vector sheaf and the actual inverse-labelled original
module operators. The compatible-module category is the existing
`CompatibleTestAction`, with original nondegenerate module morphisms that
commute with the group action. Functor equality includes all these objects
and morphisms. Natural comparison isomorphisms and the equivalence laws are
required as conclusions; none is assumed or supplied as a certificate.

`SmoothStatement` is the corresponding target for the existing full
subcategories whose entire original representations are smooth. Its forward
functor is exactly `CompactSectionActions.smoothFunctor hX`; its inverse is
exactly `SmoothProjectorActionSheaf.smoothFunctor hX hG`. The latter's
construction proves smoothness from original-vector local representatives
and their original open stabilizers, with no assumed inverse comparison.
Neither functor replaces a module by its smooth vectors. This target is the
explicit restriction of the III.3.1 identification needed for the smooth
categories in III.3.2, rather than a separately numbered source theorem.

`Statements` conjoins the two targets while retaining both full names for
focused proof tasks. Countability at infinity belongs to the later
transitive-space assertions, so it is not imposed here. These targets do
not assert the induction or singleton category equivalences or any
coinvariant fibre formula. No equivalence is proved in this module.
