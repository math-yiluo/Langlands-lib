# The divisor formula for principal ideles

`PrincipalIdeleDivisorFormula.{u}` is a proposition for every number field
`E : Type u`, every finite place `w : HeightOneSpectrum (𝓞 E)`, and every
nonzero field element represented as `a : Eˣ`. It asserts

`ideleOrder w (IdeleGroup.unitEmbedding (𝓞 E) E a) =`
`  FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E))`.

The left side uses Mathlib's actual principal idele embedding into the units
of the adele ring and the published finite-place coordinate construction. The
order is the negative of the exponent of the multiplicative completion
valuation, so that a uniformizer has order one. The right side is Mathlib's
integer prime multiplicity of the actual principal fractional ideal `a (𝓞 E)`.
The field element is nonzero because it is a unit of E; no integrality or
positivity assumption on its order is made. In particular the formula includes
negative prime multiplicities. No Galois extension, cyclic group, choice of
uniformizers or cohomological hypothesis occurs.

This is the coefficientwise principal-element compatibility needed to descend
the idele-to-fractional-ideal map to ideal classes. The statement itself does
not construct that descended map, prove quotient finiteness, or assert a
Herbrand quotient formula. This file defines the proposition and provides no
proof of it.

The original source is J. S. Milne, *Class Field Theory*, v4.03 (2020), Chapter V
§4.1 and §4.2, printed page 170 (PDF page 179), together with the ideal-class
map described at the beginning of printed page 171 (PDF page 180). Section 4.1
uses the prime powers given by local orders, and §4.2 embeds a field element
diagonally. Applying the former construction to the latter produces the
principal fractional ideal with those multiplicities. The proposition is a
derived coefficientwise formulation of this compatibility, using Mathlib's
`FractionalIdeal.count` to express prime multiplicity. Its sign also agrees
with Mathlib's `HeightOneSpectrum.intValuationDef`, which takes the exponential
of the negative prime multiplicity, and with the extension of that valuation
to the fraction field and completion.

The registered source is `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
