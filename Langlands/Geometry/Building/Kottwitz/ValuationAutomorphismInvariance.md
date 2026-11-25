# Invariance of the normalized valuation under compatible automorphisms

Notation: `F` is a nonarchimedean local field, `K = UnramifiedClosure F` is the
maximal unramified extension of `F` in `SeparableClosure F`, and `L` is an
intermediate field of `SeparableClosure F / K`. `intermediateValuation F L` is
the restriction to `L` of the spectral valuation of `SeparableClosure F`. When
`NormalizedIntermediateValuationStatement` holds,
`normalizedIntermediateValuation F L` is its unique equivalent surjective
`ℤᵐ⁰`-valued valuation (see
`Langlands/Geometry/Building/Kottwitz/NormalizedValuation.md`).

The main results say the following. Let `L/K` be finite Galois, `σ` a ring
automorphism of `K`, and `τ` a ring automorphism of `L` that restricts to `σ`. Then
`τ` preserves the spectral valuation of `L` up to equivalence. It preserves the
normalized valuation and its unit order exactly. Neither `σ` nor `τ` has to be
`K`-linear. For `K`-linear `τ` this is the familiar Galois invariance of the
valuation.

These are internal helper results for the torus Kottwitz equivariance proof.
There, `τ` is the restriction to a finite Galois splitting field of a lift to
`SeparableClosure F` of a `k`-automorphism `σ` of `K`. They do not correspond to
a numbered result of a cited source. The argument is a standard one: an
automorphism of a Henselian discretely valued field with algebraically closed
residue field preserves the valuation ring, and a valuation on a finite Galois
extension of a Henselian field is determined up to equivalence by its
restriction.

## Declarations

- `intermediateValuation_comap_algebraMap`: the restriction of
  `intermediateValuation F L` along `algebraMap K L` is `fixedFieldValuation F`.
  Both are the spectral valuation evaluated at the same element of
  `SeparableClosure F`, so the proof is `ext` followed by `rfl`.
- `fixedFieldValuation_comap_ringEquiv_isEquiv`: for every ring automorphism `σ`
  of `K`, `((fixedFieldValuation F).comap σ).IsEquiv (fixedFieldValuation F)`. The
  integer valuation `MaximalUnramified.valuation F` is equivalent to
  `fixedFieldValuation F` (`MaximalUnramified.valuation_isEquiv`). Its valuation
  ring is Henselian (`MaximalUnramified.valuationSubring_isHenselian`) and has an
  algebraically closed residue field
  (`MaximalUnramified.residueField_isAlgClosed`). Hence
  `Langlands.FieldTheory.isEquiv_comap_ringEquiv` from
  `Langlands/FieldTheory/HenselianAutomorphismValuation.lean` applies to it. The
  result is transported through the equivalence and its pullback along `σ`
  (`Valuation.IsEquiv.comap`).
- `fixedFieldValuation_isNontrivial`: `fixedFieldValuation F` is nontrivial. The
  integer valuation is surjective (`MaximalUnramified.valuation_surjective`), so
  some element has value `ofAdd (-1)`, which is neither `0` nor `1`.
  Nontriviality transfers along the equivalence (`Valuation.isNontrivial_of_isEquiv`).
- `fixedFieldValuation_valuationSubring_isHenselian`: the valuation ring of
  `fixedFieldValuation F` is a Henselian local ring. It equals the valuation ring
  of the equivalent integer valuation (`Valuation.isEquiv_iff_valuationSubring`),
  which is Henselian.
- `intermediateValuation_comap_ringEquiv_isEquiv`: assume
  `[FiniteDimensional K L] [IsGalois K L]`, let `σ : K ≃+* K` and `τ : L ≃+* L`,
  and assume `τ (algebraMap K L a) = algebraMap K L (σ a)` for all `a`. Then
  `((intermediateValuation F L).comap τ).IsEquiv (intermediateValuation F L)`.
  The proof applies `Langlands.FieldTheory.realValuation_isEquiv_of_comap_isEquiv`
  over `K` to `w₁ = intermediateValuation F L` and `w₂ = w₁.comap τ`. The
  restriction of `w₁` to `K` is `fixedFieldValuation F`, which is nontrivial and
  has a Henselian valuation ring. The compatibility hypothesis shows that the
  restriction of `w₂` to `K` is `(fixedFieldValuation F).comap σ`. That valuation
  is equivalent to `fixedFieldValuation F` by
  `fixedFieldValuation_comap_ringEquiv_isEquiv`.
- `normalizedIntermediateValuation_ringEquiv_of_comm`: under the same hypotheses
  and given `NormalizedIntermediateValuationStatement`,
  `normalizedIntermediateValuation F L (τ x) = normalizedIntermediateValuation F L x`
  for every `x : L`. The statement gives a unique normalized valuation `v`. So
  `normalizedIntermediateValuation F L` is normalized
  (`normalizedIntermediateValuation_spec`). Its pullback along `τ` is also
  normalized: it is equivalent to the pullback of `intermediateValuation F L`
  along `τ`, hence to `intermediateValuation F L` by the previous lemma, and it
  is surjective because `τ` is. Uniqueness makes the two valuations equal, and
  evaluating at `x` gives the claim.
- `orderUnits_ringEquiv_of_comm`: under the same hypotheses, the unit order
  `IntegerValuation.orderUnits (normalizedIntermediateValuation F L)` takes the
  same value at `Units.map τ a` and at `a`, for every unit `a` of `L`. Both
  sides are `-WithZero.log` of the normalized valuation
  (`IntegerValuation.orderUnits_toAdd`), and these agree by the previous lemma.

## Hypotheses

`NormalizedIntermediateValuationStatement` is an explicit hypothesis because the
statement is not yet proved in the Library. Only its instance for the given `L`
is used, both existence and uniqueness. The Galois hypothesis `IsGalois K L` is
needed by the norm argument in `realValuation_isEquiv_of_comap_isEquiv`. The
compatibility of `τ` with an automorphism of `K` is what allows Henselianity of
the valuation ring of `K`, which the Library provides, to be used. Nothing
requires the valuation ring of `L` itself to be Henselian.
