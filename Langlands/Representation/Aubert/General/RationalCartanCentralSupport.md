# Bounded actual Cartan coordinates and the full central quotient

This internal adapter implements the elementary bounded-support step in the
forward direction of Renard VI.2.1. It derives support on the quotient by the
full abstract center of the rational point group directly, without passing
through the common norm kernel.

`RationalCartanDetectionModuloCenter` names the proposition that the simple-root
coordinates determine the uniformizer classes in the full central quotient.

For a split torus in a smooth connected affine group, a generic cocharacter
with negation-stable relative roots makes the simple roots generate all relative
roots as an additive group. Evaluation against an integral cocharacter is
additive in the character. If all its simple-root evaluations vanish, the
published `rootAnnihilatorCentrality` theorem makes that cocharacter a central
scheme map. Evaluating it at the chosen uniformizer gives an element of the full
abstract point center. Applying this to the difference of two cocharacters
proves that equal simple-root coordinates determine equal quotient classes.

For a connected reductive group and a maximal split torus, the explicit
`HasRelativeRootSystem` premise supplies negation stability and finiteness of
the simple roots. Given a compact subgroup, a finite Cartan covering, and a
uniform upper bound for the simple-root coordinates of nonzero values in the
positive cone, `hasCompactSupport_centerQuotient_of_finiteCartanCovering` applies
the generic finite-image compact-support theorem. The finite covering's literal
positive cone supplies nonnegative integer coordinates. A centralizer residual
factor commutes with the torus parameter, placing the expression in the order
used by `RationalCartanSupportBound`.

The target group has its canonical rational-point topology. Its Hausdorff
topological-group hypotheses make the quotient by its full center Hausdorff.
The function's target requires only a zero. No coefficient smoothness or
Jacquet-module assertion is hidden in this result: its bound and geometric
cover are explicit premises. All results are derived from the cited Library
lemmas, rather than new source assertions.
