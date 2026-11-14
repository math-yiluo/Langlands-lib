# The zero subgroup and the cocenter

This is an internal reduction for KP Proposition 11.5.4 (Kaletha–Prasad,
*Bruhat–Tits theory: a new approach*, 2023, printed p. 431, PDF p. 462).
It retains the actual zero-subgroup datum and the full scheme-theoretic derived
subgroup.

`IsZeroPointsNormPreimage E Q q` is the property that the actual zero subgroup
from `E` is the inverse image under `q` of the norm subgroup defined with
`E.L`. Its definition accepts any affine commutative target; it does not assume
that `q` is a cocenter quotient. The theorem `zeroPoints_eq_cocenter_comap`
proves this property when `Q` is a torus, `q` is a quotient by the full derived
subgroup, and that derived subgroup is simply connected. The predicate is an
internal definition introduced to state this reusable geometric property.

For a group with simply connected derived subgroup, compare its supplied
derived representative with the one in the zero datum. Simple connectedness
makes the supplied central covering an isomorphism. The simply connected image
on rational points is therefore the derived subgroup on the identity test.
The full-kernel clause of the supplied cocenter quotient identifies this with
the rational-point kernel of the cocenter map. This argument requires no
surjectivity of the cocenter map on rational points.

For every supplied cocenter, compare it by fppf quotient uniqueness with the
published cocenter construction. The latter has a surjective cocharacter map
from the datum's maximal torus over its splitting field. KP Lemma 2.5.20,
implemented by `torusIwahoriSurjectivity`, gives the equality of norm images.
Transport along the quotient isomorphism gives this equality and the splitting
property for the supplied cocenter.

The zero subgroup is the join of the simply connected image and the torus norm
image. The former is the cocenter kernel; the latter maps onto the cocenter norm
subgroup. Elementary subgroup transport therefore identifies the zero subgroup
with its inverse image. The final two lemmas retain the full derived subgroup
under field base change, using the published derived base-change and simple
connectedness field-extension theorems.
