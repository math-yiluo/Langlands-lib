# Translation identities from rational coordinate values

This is derived supporting work by Worker 1369 for the Steinberg big-cell
construction. It introduces no external source assertion. It combines actual
affine-coordinate evaluation, reduced-scheme rational-point determination,
smoothness of products, and the earlier Frobenius root-curve cutoff.

Let k be a field in an arbitrary universe u. Let G be a group scheme affine
over Spec k. The coordinate algebra used throughout is the Library's actual
`AffineCoordinates.algebra G`, identified with global functions on G.

## Universal translation

For a group scheme H and a group homomorphism j : H → G,
`leftTranslationValue G H j b` is the global function on H × G whose value
at (h,g) is b(j(h)g). It is defined by evaluating b at the universal
product point `(fst ≫ j) * snd`. No affineness or smoothness of H is required
for this definition.

`appTop_pointAlgebraHom` writes the established naturality of coordinate
evaluation as equality of actual global sections. Applying it to the map
(h,g) from any relative test scheme proves
`appTop_leftTranslationValue`: pullback of the universal function is precisely
evaluation of b at j(h)g. Both the test scheme and its points are arbitrary.

## Determination by rational pairs

Suppose k is algebraically closed and G and H are smooth over k.
`leftInvariant_of_rationalPoints` assumes that b(j(h)g)=b(g) for every pair
of k-rational points h and g. It proves this equality for every relative test
scheme V and every h in H(V), g in G(V).

The product H × G is smooth, hence reduced and locally of finite type over
k. At each rational point z of this product, its projections are rational
points of H and G. The hypothesis therefore identifies the rational values
of `leftTranslationValue` with those of b pulled back along the second
projection. The existing `eq_of_rationalPoints` proves equality of these
global functions on H × G. Pullback along (h,g) gives the desired equality.
Only this universal product is required to be reduced. The conclusion makes
no reducedness, affineness or nonemptiness assumption on V.

## Frobenius cutoff with arbitrary translates

`leftInvariant_of_originInvariant_natDegree_lt` specializes this argument
to H equal to the actual additive group and j equal to a supplied group
homomorphism xm : Ga → G. Its hypotheses are:

- k is algebraically closed, G is smooth and affine over k, p is an
  exponential characteristic, and r is any natural number;
- b is right invariant under every intrinsic height-r Frobenius-origin
  point of G, on every relative test scheme and at every G-valued point;
- for every rational g, the actual polynomial of the curve s ↦ xm(s)g
  has natural degree strictly less than p^r.

The earlier `FrobeniusRootCurveCutoff.pointAlgebraHom_negativeCurve_eq`
gives invariance along each such curve through a fixed rational g, with
its parameter ranging over all tests. In particular it gives equality at
every rational pair (s,g). The additive group is smooth by smoothness of
its polynomial coordinate algebra. The rational-pair theorem then proves
b(xm(s)g)=b(g) for every relative test V, every additive V-point s and every
G-valued V-point g. This includes nonreduced and empty tests and height zero.

This unit retains the degree bound and origin invariance as visible premises.
It does not construct the closed translation stabilizer, extend invariance
from simple root groups to a generated unipotent group, prove the fixed-height
restriction injection, or prove `SteinbergBigCellStatement`.
