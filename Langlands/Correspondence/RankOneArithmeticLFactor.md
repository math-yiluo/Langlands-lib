# Actual rank-one arithmetic pair L-factors

For every prime `p`, every `F : PadicField p` and every supplied geometric
reciprocity candidate `e`, this internal unit computes the actual arithmetic
pair L-factor of the rank-one Weil classes attached to two continuous field
characters `χ` and `η`:

```text
arithmeticPairLFactor F
  (weilPairClass F (rankOneWeilCharacterClass F e χ))
  (weilPairClass F (rankOneWeilCharacterClass F e η))
  = PadicAbelian.rationalLFactor F.canonicalTopologicalData (χ * η).
```

The field and parameter-carrier universes remain independent. There is no
unramifiedness assumption on either character or their product.
`arithmeticPairLFactor_of_isRankOneWeilCharacter` gives the same formula for any
two actual rank-one Weil classes realizing those characters, using the existing
class-uniqueness theorem.

`isUnramifiedQuasicharacter_iff_isUnramifiedCharacter` first compares the two
published definitions of unramifiedness: triviality on valuation-zero units and
triviality on the kernel of the normalized order. The existing normalized
absolute value and valuation comparisons identify those subgroups.
`weilCharacter_trivial_on_inertia_iff` then proves that the pulled-back character
is trivial on actual local inertia exactly when the field character is
unramified. One direction uses the geometric reciprocity order formula and
surjectivity of `reciprocityHom`; the other uses the published inertia comparison.
The reciprocity map and its geometric property are supplied hypotheses.

`eulerPolynomial_scalarWeilCharacter` computes the actual inertia-fixed
monodromy-kernel Euler polynomial at the published geometric Frobenius. If the
field character has conductor zero, the scalar inertia action is trivial and the
Frobenius comparison gives
`1 - C (χ (uniformizerUnit F.canonicalTopologicalData) : ℂ) * X`.
Otherwise, inertia acts nontrivially on the scalar line, so the fixed kernel
vanishes and the Euler polynomial is `1`. These are precisely the two branches
of `PadicAbelian.lPolynomial`. Taking the inverse of its image in `RatFunc ℂ`
gives `rationalLFactor_scalarWeilCharacter`, retaining poles as rational
functions.

The class-level pair proof unfolds the chosen class representatives to lifted
character lines. `WeilDeligneRepresentation.tensorCongr` transports tensor
equivalences across four independent carrier universes. Its linear equivalence
is `TensorProduct.congr`; the existing `tensorMap` supplies equivariance and
monodromy compatibility. Composing this transport with the scalar tensor
multiplication equivalence identifies the actual tensor pair with the scalar
pair for the product character. Invariance of the rational L-factor under
genuine pair equivalence and the scalar formula finish the proof.

This is derived internal content using the published representation, quotient,
reciprocity-comparison, conductor and Euler-polynomial constructions. It uses no
additional literature assertion. It does not prove existence of geometric
reciprocity, an automorphic JPSS comparison, any epsilon-factor comparison, or
the closed all-field correspondence proposition.
