# Supports of Tadić's multisegments `a(n,d)^ρ`

Author: Worker 1792. Module
`Langlands.Representation.Classification.TadicSupportIdentification`, namespace
`Langlands.Classification`. Everything is proved from published Library results;
there are no hypotheses of theorem type, no axioms and no `sorry`.

This module formalizes the support step of Tadić's proof of Theorem A.10 (1986,
printed p.379): once `L(a(n,d)^ρ) = ⟨a(u,v)^σ⟩` with `ρ, σ` unitary, comparing
supports gives `L(a(n,d)^ρ) ∈ {⟨a(n,d)^ρ⟩, ⟨a(d,n)^ρ⟩}`.

## Unitary twist rigidity

- `cuspidalDatum_twist_isUnitary_eq_zero`: if `ρ` and `ν^s ρ` are both unitary
  cuspidal data, then `s = 0`. Proof: take a representative `A` of `ρ` and its
  twist `A_s` by `|det|^s`. Both are irreducible, admissible and unitarizable, so
  the proved `unitarizableCentralCharacter` gives unitary central characters `ω`,
  `ω_s`. On a nonzero vector, the scalar uniformizer `ϖ` acts on `A_s` by
  `|det ϖ|^s ω(ϖ) = q^(-r s) ω(ϖ)` (`IntegralTwistFreeness.scalar_uniformizer_value`)
  and by `ω_s(ϖ)`. Taking absolute values gives `q^(-r s) = 1`, so `r s = 0` and
  `s = 0` since `q > 1` and `r > 0`.
- `cuspidalDatum_eq_of_twist_eq_of_isUnitary`: for unitary `ρ, τ`,
  `ν^s τ = ν^t ρ` implies `τ = ρ` and `s = t`.

## Cuspidal content of `a(n,d)^ρ`

- `mem_cuspidalContent_tadicMultisegment`: the published `Multisegment.cuspidalContent`
  of `a(n,d)^ρ` consists of the `ν^(i + j - (n-1)/2 - (d-1)/2) ρ` with `j < n`,
  `i < d`.
- `card_cuspidalContent_tadicMultisegment`: it has `n * d` elements with
  multiplicity.

## Supports of heads and socles

- `SegmentProductDatum.isSupercuspidalSupport_of_isLanglandsHead`: a Langlands
  head of a precedence-ordered product of segment heads has the cuspidal content
  of the datum's multisegment as supercuspidal support (`IsSupercuspidalSupport`).
  The proved `segmentHeadProductCuspidalQuotient` presents `E.induced` as a
  quotient of the cuspidal product of all segment members; composing with the
  head quotient map shows that the head is an irreducible quotient, hence a
  subquotient, of that cuspidal product.
- `SegmentProductDatum.isSupercuspidalSupport_of_isZelevinskySocle`: the same for
  Zelevinsky socles, by the proved
  `SegmentSocleDerivativeConstituentSupport.support_of_product` applied to the
  socle embedding.
- `isSupercuspidalSupport_of_isLanglandsHead`,
  `isSupercuspidalSupport_of_isZelevinskySocle`: the multisegment forms.

## Identification of the parameters

- `tadicMaxExponent_le_of_cuspidalContent_eq`: if `a(u,v)^ρ` and `a(n,d)^ρ` have
  the same cuspidal content, then `(u-1)/2 + (v-1)/2 ≤ (n-1)/2 + (d-1)/2`. The
  member with the largest exponent of `a(u,v)^ρ` is a member of `a(n,d)^ρ`, and
  exponents are compared with `cuspidalDatum_twist_injective`.
- `tadic_parameters_of_cuspidalContent_eq`: for unitary `τ, ρ` and positive
  `u, v, n, d`, equal cuspidal contents of `a(u,v)^τ` and `a(n,d)^ρ` give
  `τ = ρ` and `(u, v) = (n, d)` or `(u, v) = (d, n)`. A member of the first content
  is `ν^x τ = ν^y ρ`, so `τ = ρ` by rigidity. The maximal exponents agree, so
  `u + v = n + d`; the cardinalities give `u v = n d`; hence
  `(u - n)(u - d) = 0`.
- `tadic_parameters_of_isZelevinskySocle_of_isLanglandsHead`: if `π` on `GL_N` is
  a Zelevinsky socle of `a(u,v)^τ` and a Langlands head of `a(n,d)^ρ` (all
  parameters positive, `τ`, `ρ` unitary), then `τ = ρ` and `{u, v} = {n, d}`.
  Both contents are supercuspidal supports of the irreducible `π`; the proved
  `glSupercuspidalSupportUniqueness` makes them equal.
