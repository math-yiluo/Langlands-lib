# Rational Harris determinant pullback and its actual moduli subpresheaf

Author: Worker 57.

This internal construction transports the existing actual rational Lie
determinant condition along arbitrary scheme morphisms. The comparison uses
the named `LieBaseChangeNaturalityStatement`, which remains an explicit
hypothesis. The module does not supply the proof of that integral naturality
statement.

The generic lemmas use arbitrary same-universe schemes and an actual map
`p : S → Spec R` with `R` a rational algebra. Polynomial overlap is proved
by basis independence for the same actual rational section endomorphisms.
The polynomial pullback formula uses the constructed `lieBaseChangeChart`,
the actual rational order pullback, and the rational action square proved in
`LieRationalBaseChange`. Actual matrix and polynomial pullback transport
then gives equality under the structure-sheaf coefficient map.

For the existing Harris data, reflex field and integral order,
`harrisRationalOrderAction_baseChange` identifies restriction of the
pulled-back rational algebra action with pullback of the restricted order
action. Local determinant stability follows from the generic formula and
the proved pullback law of the reflex polynomial's actual section
coefficients.

All-chart stability uses the actual finite local Lie trivializations on
the source. Their inverse-image opens cover the target. Each constructed
chart satisfies the pulled-back test. Restriction to intersections and
chart-overlap independence supply the test on each member of a cover of
an arbitrary target chart open. Sheaf separation applied to each
polynomial coefficient proves the test on that open. There is no flatness,
reducedness or affine-base restriction.

The existing condition on rational action isomorphism classes therefore
survives actual pullback. The proof selects a representative only to
apply the all-chart theorem; the underlying class pullback is the existing
quotient map induced by the actual action-category pullback.

With an explicit family of the same named integral naturality statements,
`harrisRationalLieDeterminantSubfunctor` restricts the existing presheaf of
actual rational algebra-action classes on schemes over the actual reflex
spectrum. Its object predicate is exactly the existing all-chart
determinant class condition. For a morphism of schemes over that spectrum,
the proved stability theorem applies to the actual underlying scheme
map, and the over-category triangle identifies the target structure map.

`harrisRationalLieDeterminantPresheaf` is the resulting subtype presheaf.
Its identity and composition laws are the laws of `Subfunctor.toFunctor`,
using those of the existing actual class presheaf. The object formula
identifies its values with the existing determinant class subtype. The
map and representative formulas retain actual abelian-scheme pullback
and its actual rational endomorphism action. The inclusion is the
subfunctor's natural inclusion and is injective at every object.

The provenance is internal: basis independence, actual rational Lie
naturality under its named hypothesis, actual coefficient pullback and
coefficientwise sheaf separation. No new external theorem is asserted.
This presheaf includes abelian schemes, rational algebra actions and the
determinant test. Polarizations, level structures, the Harris--Taylor
numerical test, representability and scheme levels remain additional
constructions required for the full Harris PEL problem.
