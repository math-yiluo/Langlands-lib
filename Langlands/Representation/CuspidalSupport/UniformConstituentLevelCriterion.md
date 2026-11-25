# A criterion for one compact-open constituent detector

`Langlands.SmoothRep.UniformConstituentLevelCriterionStatement` is a
derived intermediate criterion, not the full complex or coefficient-family
finite-type characterization. It concerns a smooth complex representation
`A` of a first-countable weakly locally compact nonarchimedean group.
It has two explicit hypotheses:

- Every irreducible actual subquotient of `A` is centre admissible.
- Every centre-admissible countable direct sum of irreducible actual
  subquotients of `A` is finitely generated over the group algebra.

The conclusion is existence of one compact open subgroup with nonzero
fixed vectors in every irreducible actual subquotient of `A`. Neither
of the two hypotheses is asserted unconditionally in this module.

The implemented proof chooses a decreasing compact-open neighbourhood
basis. If no uniform detector exists, at its `n`th level choose an
irreducible subquotient `D n` with zero fixed space at that level.
For any open subgroup `L`, some basis subgroup is contained in `L`;
all later `D n` consequently have zero `L`-fixed space. The companion
direct-sum helper makes the actual sum of these `D n` centre admissible.
The second hypothesis makes this sum finitely generated, contradicting
the helper's obstruction for infinitely many nonzero summands.
Irreducibility supplies nonzero carriers.

Provenance is internal and derived from this countable-sum contradiction,
as a step toward David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026, VI.10.7, Proposition and Variant
(printed pp.216–217 / PDF pp.222–223), source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard does not state this criterion separately. A consumer must supply
the two hypotheses from proved results; this criterion does not assume
that an unproved complex characterization has already been proved.
