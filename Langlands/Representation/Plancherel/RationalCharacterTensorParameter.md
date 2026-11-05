# Rational-character tensors and actual complex exponential parameters

Worker 6. This is a construction prerequisite for the tensor description in
David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, V.3.19–V.3.20, printed pages 115–116 / PDF pages 121–122.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Actual objects and construction

Let \(F\) be any nonarchimedean local field under the existing field,
valuation and topology assumptions, and let \(G\) be an actual group scheme
over \(F\). The source's character group is the existing
`GroupScheme.rationalCharacters G`. Its integer-valued evaluations are the
existing `rationalCharacterValuation G`, and the discrete image is the actual
range `rationalDiscreteValuationImage G`. No replacement lattice, valuation
or point group is supplied as a new input.

`rationalCharacterImageComplexFunctional` sends a rational algebraic character
\(\chi\) to the additive functional \(a\mapsto a(\chi)\), with its integer value
included in \(\mathbb C\). It uses the published integer-linear inclusion
`rationalImageIntegerDual`. Additivity in the image element and the
character gives the integer-linear map.

`rationalCharacterTensorParameter` extends this map to a complex-linear map

\[
\mathbb C\otimes_{\mathbb Z} X^*(G)
  \longrightarrow \operatorname{Hom}_{\mathbb Z}(\Lambda(G),\mathbb C).
\]

Here \(\Lambda(G)\) denotes the actual valuation image. The construction uses
`AlgebraTensorModule.lift` and has the proved evaluation formula
\((s\otimes\chi)(a)=s\,a(\chi)\). Mathlib puts the scalar in the first tensor
factor to give its standard complex module structure. Tensor commutation
identifies this convention with Renard's notation \(\chi\otimes s\).

`rationalCharacterTensorExponential` composes with the existing actual-image
complex exponential. Its value on a pure tensor is
\(\exp(-s\,a(\chi)\log q)\), where \(q\) is the actual residue cardinality.
Both maps are bundled homomorphisms, so their zero and addition laws are
already encoded in their types.

## Formula on actual rational points

When \(G\) is affine and locally of finite type, the canonical rational-point
topology and the existing canonical unramified-character construction are
available. `rationalCanonicalCharacterTensorExponential` composes the same
linear map with that canonical exponential. The theorem
`rationalCanonicalCharacterTensorExponential_tmul_val` proves, for every
actual rational point \(g\),

\[
e^{s\otimes\chi}(g)=|\chi(g)|_F^{\,s}.
\]

The right side uses `LocalField.residueNormalizedAbsoluteValue F`, the
published actual character evaluation, and Mathlib's complex power. Since
character evaluations are units, their normalized absolute values are
positive. The proof uses `fieldNormUnits_rpow` to write this positive value as
\(q^{-v_F(\chi(g))}\), takes its real logarithm using `Real.log_rpow`,
identifies the complex logarithm of this positive real number by
`Complex.ofReal_log`, and rewrites complex power by
`Complex.cpow_def_of_ne_zero`. Commutativity of complex multiplication
identifies the resulting exponent with the existing exponential parameter.
No branch choice for a nonpositive base is needed.

## Provenance and retained obligations

The pure-tensor formula is explicitly asserted in Renard V.3.20 on printed
page 116. The canonical linear map and its scalar-first implementation are
the direct evaluation construction underlying that assertion. Their scope
extends to any group scheme under the listed field assumptions; the formula
on canonical rational points adds only affineness and local finite type.
There is no reductivity, splitting, characteristic-zero or rank premise.

This pair does not prove that the tensor map is injective or surjective.
Identification with the whole complex image dual, equality of lattice ranks,
comparison with a split center, algebraic-torus representability and manifold
structure remain separate obligations. The existing exponential is normalized
as \(q^{-s}\); the pair makes no identification with the distinct raw natural
logarithm convention discussed after the exponential in the source.
