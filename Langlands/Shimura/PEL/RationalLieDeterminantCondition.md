# The Harris section determinant condition for actual rational algebra actions

This is a derived rational-action version of
[LieDeterminantCondition](LieDeterminantCondition.md), using the actual
rational Lie functor and its section determinants. It retains the same
constructed order, reflex determinant and reflex-field base morphism.
Worker 57 authored this unit.

The arithmetic input is the existing actual central simple unitary datum
`D`, Harris signature charts `C` and CM-section hypothesis `hΦ`. The actual
base scheme `S` maps by `s` to the spectrum of the constructed cocharacter
reflex field. An actual abelian scheme `B` over `S` carries an actual
rational algebra map `i : A →ₐ[ℚ] End0 B`. This unit does not require or
prove injectivity of `i`.

`harrisRationalOrderAction` restricts this map along the inclusion of
`D.harrisHodgePELIntegralOrder C` into `A`. It takes values in actual
rational endomorphisms of `B`. The rational algebra structure on the reflex
field and the actual base morphism `s` provide the rational scalars used
by `lieRationalSectionDeterminant`.

`HarrisRationalLieDeterminantConditionAt` equates that constructed Lie
polynomial for a finite order family to the existing
`harrisReflexSectionDeterminant`, on the same smaller open of the same
finite Lie chart. Both polynomials have coefficients in the actual
structure sheaf. The coefficientwise equivalence keeps every monomial,
and restriction uses the actual structure-sheaf maps. Evaluating the
equality gives the intrinsic determinant identity for every scalar tuple.
No reducedness or nonzero-ring assumption is used.

`HarrisRationalLieDeterminantCondition` quantifies every finite family in
the constructed order, every finite Lie chart and every smaller open.
If an actual integral action `α` agrees with `i` on that order after
`endToEnd0 B`, both the local and the global predicates are equivalent
to the published integral-action conditions. These equivalences follow
from the proved integral specialization of the rational Lie polynomial.
The existence of a compatible integral action is not assumed silently.

For an actual rational isomorphism `e : of B ≅ of B'` intertwining the
actual algebra actions for all elements of `A`, the local conditions
are equivalent for any finite charts on the same open. This follows
from `lieRationalSectionDeterminant_iso`; the reflex sides are identical.
The global equivalence covers all target charts. For each target chart,
the proof composes it with the inverse of the restricted actual
`lieIso0 s e` to obtain a source chart. In the reverse direction it
composes a source chart with that isomorphism to obtain a target chart.
No chosen covering or selected list of charts replaces the universal
quantification.

The rational-action requirement is motivated by Harris and Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties*, Annals
of Mathematics Studies 151 (2001), III.1, printed pp.90–91 (PDF pp.98–99),
registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`.
In particular, p.91 uses an action in `End0` and isogeny equivalence in
the characteristic-zero moduli problem. The reflex polynomial is the
existing construction derived from Kottwitz, *Points on Some Shimura
Varieties over Finite Fields* (1992), section 5, printed pp.389–391,
registered source `kottwitz-1992-points-shimura-finite-fields`.

This unit is an internal extension and invariance theorem for the
Library's reflex-field determinant predicate on order families. It
does not identify that predicate with the full Harris–Taylor
compatibility conditions or construct the full moduli problem.
Polarizations, Tate levels, geometric-point independence and
representability are separate obligations. The rational isomorphism
includes an actual inverse; invertibility of arbitrary isogenies is
not asserted. All types have universe zero, as in the existing Harris
reflex polynomial and integral condition.
