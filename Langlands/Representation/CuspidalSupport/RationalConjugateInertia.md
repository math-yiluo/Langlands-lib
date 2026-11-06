# Actual algebraic conjugacy and rational inertia transport

Author: Worker 1153.

This internal construction supplies the transport algebra used to implement
Renard, *Représentations des groupes réductifs p-adiques* (2026), VI.7.1,
printed pp. 180–181 / PDF pp. 186–187, registered source
`renard-2026-representations-groupes-reductifs-padiques`.
It makes no cuspidal-support or Bernstein-decomposition assertion.

`rationalPointIso` is the point homeomorphism of an actual algebraic group
isomorphism in the canonical rational-point topology. Its same-carrier smooth
pullback has proved identity, composition and inverse isomorphisms. Pullback
commutes with the existing same-carrier `rationalUnramifiedTwist`, using
`rationalUnramifiedCharacterRestrict` on the full family of actual rational
characters. Consequently actual inertia equivalence is preserved by algebraic
pullback, and the source-side and target-side transported-orbit formulations
are equivalent. These are elementary internal consequences of the published
pullback, twist and character-restriction constructions; no source theorem
about induction is used.

`RationalLeviConjugacy j k` contains an ambient rational point `g`, an actual
group-scheme isomorphism `e` between the two embedded groups, and the equation
`j ≫ Int(g) = e.hom ≫ k`. This equation says on **every** test scheme that the
embedding of `e(x)` is `g x g⁻¹`, with `g` pulled back from the base. Thus this
is algebraic Levi conjugacy, not an arbitrary equivalence of point groups.
Its proved identity, inverse and composition constructions use respectively
`1`, `g⁻¹` and `h g`, and the corresponding algebraic isomorphisms.

The field/group universe and the representation-carrier universe are independent.
Affineness gives the canonical topologies; local finite type is required only
where the existing open-kernel rational twist is used. Irreducibility,
admissibility, finite length and connected reductivity are not required for
these transport lemmas. The later actual-standard-family specialization adds
the geometric and cuspidality hypotheses.
