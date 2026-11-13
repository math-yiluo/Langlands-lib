# The shifted highest derivative of a unitarizable `⟨a⟩`

Author: Worker 5121. Module `Langlands.Representation.Classification.TadicBlockDerivative`,
namespace `Langlands.Classification.TadicBlockDerivative`. Helper module of the proof of
`Langlands.Classification.TadicBlockReductionFromInputs`.

## Results

- `nonempty_iso_of_isSubquotient`: an irreducible subquotient of an irreducible
  representation of `GL_N` is isomorphic to it. Proof through classes: the composition
  multiplicity is positive (`compositionMultiplicity_pos_iff_isSubquotient`), so the label of
  the subquotient has positive coefficient in the basis class of the irreducible, hence equals
  its label.
- `isZelevinskySocle_of_isZelevinskySubrepresentation`: an irreducible subrepresentation of a
  nonprecedence-ordered product of segment socles is a Zelevinsky socle of its multisegment
  (the product has an irreducible socle by the published `orderedMultisegmentSocleExistence`).
- `exists_shiftedHighestDerivative_socle`: assume `BernsteinShiftedHighestDerivativeUnitarity`
  (Tadić 1986, Theorem 2.5(iii)). For an irreducible unitarizable `π` of `GL_N`, `N > 0`, and
  a multisegment `a` with `a.IsZelevinskySocle π`, there are `M < N` and an irreducible
  unitarizable `π'` of `GL_M` with `(dropLast a).degree = M`, and, if `M > 0`,
  `((dropLast a).twist (1/2)).IsZelevinskySocle π'`.

## Proof of the last result

Write `π` as the socle of a precedence-ordered product `d.induced` of segment socles with
multisegment `a`, and let `λ = ∑ rank(Δ_i)`. The published label step
`highestDerivativeLabelStep` (weak form of Zelevinsky 1980, Theorem 6.6) gives an irreducible
subquotient `π''` of the order-`λ` derivative of `π` that is a Zelevinsky subrepresentation
of a datum with multisegment `a⁻ = dropLast a`. Derivatives of order `j > λ` of `π` vanish:
they embed (published exactness `generalLinearDerivativeExactness`) into those of
`d.induced`, which vanish by the published `segmentSocleProductHighestDerivative`. Hence `λ`
is the highest derivative order, recorded as `GeneralLinearHighestDerivativeOrderData`.
Bernstein's Theorem 2.5(iii) makes `ν^(1/2) π^(λ)` irreducible and unitarizable; by
`isIrreducible_twist_iff` the derivative `π^(λ)` is irreducible, so `π'' ≅ π^(λ)` and
`π^(λ)` is a Zelevinsky socle of `a⁻`. Its degree is `N - λ < N`. For positive degree the
published real-twist compatibility `multisegmentConstituentRealTwistCompatibility` turns this
into `(a⁻.twist (1/2)).IsZelevinskySocle (ν^(1/2) π^(λ))`.

## Sources

Tadić 1986 (`tadic-1986-unitary`), Theorem 2.5(iii) (p.346) with §1.16; Zelevinsky 1980,
Theorem 8.1 (p.195), whose conclusion `π^- = ⟨a⁻⟩` is recovered here from the weak label form
and the irreducibility supplied by Bernstein's theorem.
