# Shallow positive-depth standard models of induced tori

`InducedTorusShallow.standardModel F R r hR hr hr₁` constructs an
`IntegralModel` of an induced torus \(R\) over the maximal unramified field
\(K\) of a nonarchimedean local field \(F\). Its base is
`fixedFieldIntegers F`. The value includes proofs of smoothness,
geometric connectedness of every fibre, and the literal subgroup equality
`M.integralPoints = localGeometricCharacterCongruence F R r` for
\(0<r<1\).

For a Weil restriction from a finite product of coefficient fields,
`modelOfFactors` starts with the product of their integer rings. The
normalized additive valuation defines an ideal of this algebra. The base
uniformizer, of normalized value one, belongs to the ideal in the shallow
range. `WeilCongruence.integralModel` builds the resulting model as the
kernel of the split first projection from the multiplicative Weil
restriction of the congruence-pair algebra. This split projection gives a
retraction over the integer ring and over every field-valued fibre, which
provides smoothness and geometric connectedness. Inverting the base
uniformizer identifies the generic kernel with the original Weil
restriction, using the second projection.

On integral sections the second component is a unit congruent to one
modulo the depth ideal. Conversely, the positive-depth inequality on a
rational unit minus one forces value zero on the unit. Thus each coordinate
is a unit of its integer ring, and the coordinates give a point of the
kernel model. `mem_geometricCharacterCongruence_iff` identifies these
coordinate bounds with the normalized geometric-character condition.
`modelOfFactors_integralPoints` combines these two comparisons.

For arbitrary \(R\), `standardModel` chooses a finite Galois splitting field
and applies `inducedTorusWeilDecomposition`. It embeds the intermediate
coefficient fields in the fixed separable closure and uses their product
model. Composing the generic identification with the resulting torus
isomorphism transports the integral-point image. Functoriality in both
directions of the isomorphism transports the geometric-character subgroup.
The construction applies to wild factors, residue characteristic two, and
the trivial torus. It realizes `InducedTorusShallowModelStatement`.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition B.3.6(1) and its proof, printed pp. 658–659 (one-based PDF
pp. 689–690). The split kernel gives a coordinate construction of the
multiplicative congruence model used in the proof, via the valuation ideal
on the integral coefficient algebra.

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
