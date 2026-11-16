# The discrete-series coefficient sum with fixed central character

Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
VIII.4, printed p.330 (PDF p.96), defines `A₂(G)_χ` as the sum of the
coefficient spaces of discrete-series classes whose central character
restricts to `χ` on the split component. Theorem VIII.4.2 on pp.330–331
identifies this sum with the central projection of the cuspidal Schwartz
space. This module constructs the sum and proves elementary algebraic
properties. It does not prove that analytic identification.

## Construction and hypotheses

`discreteSeriesCentralCoefficientSpace A hA mu χ` is the supremum of the
published `coefficientFunctionSpace ω.val.out.obj`, indexed by the subtype
of `DiscreteSeriesClass A hA mu` satisfying `classActsByCharacter A χ ω.val`.
A supremum of submodules is the algebraic sum: its elements are finite sums
of vectors from these coefficient spaces. It imposes no analytic
decomposition or finiteness of the indexing set.

The group is any topological group `G : Type uG`. The subgroup `A` is normal
and central. The measure `mu` is a Haar measure on the supplied measurable
quotient `G / A`. The discrete-series condition is exactly the existing
square-integrability-modulo-central-subgroup condition, on this same
quotient and measure. For the rational-point application, `A` is the image
of the split component and the quotient has its Borel measurable space.
The character is a monoid homomorphism `A →* ℂˣ`; no additional restriction
is needed for this algebraic construction.

The representation carrier universe `uV` is independent of `uG`.
The coefficient transport lemma also permits a second independent
representation universe `uW`. The construction introduces no field,
splitness, quasi-splitness or rank assumption.

## Elementary results and provenance

The summand inclusion and matrix-coefficient membership theorem include
every canonical smooth coefficient of each eligible class. The
`_le_iff` theorem gives the least-submodule property.

`coefficientFunctionSpace_eq_of_equiv` uses the published tensor
description of the coefficient space, transports tensors by
`coefficientTensorCongr`, and applies `coefficientTensorMap_congr` in
both directions. Thus equivalent smooth representations have literally
equal spaces of functions on `G`, even across carrier universes.
`coefficientFunctionSpace_eq_out_of_class_eq` applies that fact to a
representative of a smooth-dual class. The `_eq_iSup_representatives`
theorem proves that choosing any irreducible admissible representative
for every class gives exactly the same algebraic sum.

`iSupIndep_discreteSeriesCentralCoefficientSpace` imports
`iSupIndep_coefficientFunctionSpace`: each chosen representative is
irreducible, and an equivalence identifies its smooth-dual class and
then the nested subtype indices. Thus the coefficient summands are
independent. Finally, the published
`discreteSeriesCentralFixedCoefficientSpace` is contained in this sum by
its least-span property. This inclusion says nothing about lifting a
coefficient through a central integral with the same compact-open level.

These are internal algebraic constructions and derived proofs from the
published canonical coefficient tensor and independence interfaces.
The source's `A₂` sum motivates their definition. Theorem VIII.4.2 and
the level-preserving inclusion used in VIII.5 remain separate analytic
targets.
