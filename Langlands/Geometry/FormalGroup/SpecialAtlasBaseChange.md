# Coefficient extension of order actions and special formal atlases

This module extends the actual division-order action, special tangent
characters and scalar-kernel height certificates of a supplied formal atlas
along an arbitrary coefficient extension.

## Source and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), permits formal groups glued over localizations just before
section 2. Section 2 A defines special formal division-order modules by
dimension d and distinct geometric tangent characters, then requires height
d² for the objects of the moduli functor. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The coefficient constructions and preservation results here are internal
consequences of the existing formal laws, order actions and special tangent
conditions; they are not separate numbered assertions of that article.

The first namespace uses arbitrary commutative rings O and R, an O-algebra
structure on R, any O-algebra D whose ring need not be commutative, and an
actual atlas X with a fixed finite coordinate type in `Type`. It assumes an
actual atlas order action E and `S : CommAlgCat.{v} R`. Coefficient tests have
universe v. The image cover and its chosen generator preimages are exactly
those of `AtlasBaseChange`; neither injectivity nor flatness is required.

The special namespace uses a nonarchimedean local field K, an arbitrary
finite-dimensional central division K-algebra D, and a supplied embedded
field L as in `SpecialAtlas`. Set d = `CentralSimple.reducedDegree K D`.
The original atlas supplies the explicit unramified full-degree integer
subfield condition and the distinct geometric tangent characters. The
coordinate type is `Fin d`. Geometric fields have universe `max u v`, as
in `SpecialModule`. Existence of the unramified subfield and specialization
to invariant 1/d remain separate obligations.

## Actual order actions and chart comparisons

`BasicAtlas.OrderAction.baseOrderChart` extends the chosen original chart's
actual formal D-action along `baseChartCoefficient`. The two coefficient
routes to any S-algebra test agree. Mapping the coordinate series along this
triangle proves `baseOrderChart_coordinates` for every element of D.

`baseOrderChartIso` upgrades the actual identity-coordinate formal chart
comparison to a D-linear formal isomorphism. The action-series equality
proves linearity of both formal inverse maps. The inverse equations are
those of the underlying formal-module chart comparison.

`baseOrderTransition` proves that the extended actions commute with the
actual conjugated transitions. Extensionality reduces this to coordinate
series; the transition series are the original transition series, and the
extended action series are the original action series on the restricted
test. The original formal commutation equation therefore proves the new
one. `baseChange` packages the actual action on `X.baseChange S`.

`baseChangeChartEquiv` evaluates the constructed order-linear formal
isomorphism. It compares one new chart's points with its chosen original
chart's points on the restricted test. The `apply` and `symm_apply` lemmas
prove that both directions preserve the actual nilpotent coordinate tuple:
each evaluates identity coordinates.

## Specialness and actual height

`SpecialAtlas.baseChange` uses the new atlas and order action. It retains
the same embedded unramified field and extends each chosen original
geometric tangent-character condition along the actual localization map,
using the existing coefficient-extension theorem.

`baseChange_height` preserves `HasHeightSquared pi`. Its hypotheses include
irreducibility of pi in O_K, nilpotence of its actual image in R, and actual
`HasPiHeight pi q (d^2)` certificates on every original chart, where
q = `Nat.card` of the residue field of K. Irreducibility is unchanged;
the ring map R → S preserves nilpotence; the existing scalar-kernel
coefficient theorem extends each chosen chart's fppf, torsion, finite
projective kernel-algebra and stalk-rank certificate. Specialness alone
does not supply these height certificates.

`SpecialAtlas.baseChangeChartEquiv` specializes the constructed chart
comparison to a linear equivalence over the actual division order
`IntegerRing K D`.

This unit compares individual charts. It asserts no full compatible-family
point comparison, independence of generator choices, iterated base change,
refinement descent, equivalence with all formal schemes, framing module,
Drinfeld moduli functor or representability.
