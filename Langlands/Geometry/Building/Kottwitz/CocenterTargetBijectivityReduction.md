# Integral cocenter target bijectivity

This internal reduction continues the integral cocenter comparison of
`CocenterCocharacterExactness`. Its source motivation is Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), §11.5, printed pp.429–430
(PDF pp.460–461), where the quotient by the simply connected derived group
induces the fundamental-group identification used in the cocenter square.
The registered 2024 corrections, PDF pp.43–45, concern §11.7 and do not
change that passage.

For an actual fundamental-group choice, an actual cocenter, and a field
splitting the chosen maximal torus, `cocenterInertiaEquiv` is an integral
linear equivalence from the inertia coinvariants of that choice's quotient
to the inertia coinvariants of the cocenter's actual cocharacters. The
derived group is assumed simply connected.

The existing integral cocharacter equivalence is Galois equivariant:
quotient induction reduces this to its representative law and naturality
of Galois transport for the actual quotient morphism. Its inverse is also
equivariant, by injectivity of the forward equivalence. Descending the
two intertwining linear maps gives mutually inverse maps on the actual
inertia coinvariants. Their compositions are checked on quotient
representatives. The projection theorem records the resulting law.

The remaining theorems retain five explicit Library statement hypotheses:
algebraic fundamental-group comparison and map statements, the torus
fundamental comparison statement, the fundamental inertia map statement,
and the torus inertia comparison statement. These are mathematical inputs,
not conclusions supplied by this module.

Under the first three inputs, `cocenterCocharacterEquiv_eq_selected`
identifies the chosen cocharacter equivalence with the selected
fundamental-group map of the quotient followed by the selected torus
comparison. For a torus target its chosen maximal-torus inclusion is an
isomorphism. Its inverse gives an actual factorization of the quotient's
restriction. The induced-map representative law, identity comparison law,
and torus comparison representative law then reduce the equality to
functoriality of base change and cancellation of that inverse.

Under all five inputs, `cocenterInertiaMap_bijective_of_statements` identifies
the selected inertia-map composite with `cocenterInertiaEquiv`, using the
two inertia representative laws and surjectivity of the quotient
projection. Splitting over the supplied separable closure is obtained
from the published separably closed group-like spanning theorem and the
actual torus base-change theorem. Thus the selected composite is
bijective. `cocenterTargetMap_bijective_of_statements` specializes this
result to the coefficient tower of the Kottwitz construction.

All quotients and equivalences are integral; no torsion is discarded.
The five comparison/descent inputs are still assumptions. This unit
does not prove the unconditional simply-connected-derived Kottwitz
statement, the torus Kottwitz laws, or surjectivity of the cocenter
Kottwitz composite on actual field points.
