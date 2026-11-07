# Whittaker completeness: the unlinked supercuspidal base case

This supporting module provides the base case of the proof of Whittaker completeness
(`Langlands.Whittaker.WhittakerCompletenessStatement`, Jacquet and Shalika 1985,
`jacquet-shalika-1985-ramified-factors`, Lemma (3.2), printed page 325). It does
not prove that statement by itself.

The proof of the statement is by induction on the number of linked pairs among the
supercuspidal blocks `τ_1, …, τ_k` of a normalized product, which reduces it to the
Library proposition `SupercuspidalProductCompletenessStatement`. The induction is
written separately. This module handles the case with no linked pair. There the
product is irreducible and generic, so the completeness hypothesis, which is stated
for generic representations, applies to its Whittaker functions directly.

## Conventions

`ν = |det|` is the character `T.determinantPowerCharacter n 1`. A cuspidal datum
`PadicField.TopologicalData.CuspidalDatum.{uW, uF} T` is Zelevinsky's element of
`𝒞`: a rank `r > 0` together with an isomorphism class of irreducible supercuspidal
representations of `GL_r(F)` with carrier in `Type uW`. `ρ.twist s` is the class of
`ρ ⊗ ν^s`. `F.canonicalNormalizedProductInduced (succBlockShape m h) τ` is the
normalized parabolic induction to `GL_(t+1)(F)` of the external tensor product of
the blocks `τ i` of `GL_(m i + 1)(F)`, where `h : ∑ i, (m i + 1) = t + 1`. In the
namespace `Langlands.Whittaker` the canonical topology, valuation and local-field
structures of `F` are local instances.

## Declarations

### Cuspidal data of blocks

- `PadicField.TopologicalData.supercuspidalDatum T hn τ hs hirr hsc` is the
  cuspidal datum of a smooth (`hs`), irreducible (`hirr`) and supercuspidal (`hsc`)
  representation `τ` of `GL_n(F)`, `0 < n`. It has rank `n`
  (`supercuspidalDatum_rank`) and class the isomorphism class of the supercuspidal
  object `⟨SmoothRep.of τ hs, hirr, hsc⟩`.
- `supercuspidalDatum_twist`: the datum of `τ ⊗ |det|^s`, for any proofs of its
  three properties, is `(supercuspidalDatum τ).twist s`. This holds by `rfl`.
- `Langlands.Whittaker.blockDatum τ hs hirr hsc a` is the datum of the block `τ a`
  of `GL_(m a + 1)(F)` for the canonical structures. It is
  `supercuspidalDatum (Nat.succ_pos (m a)) (τ a) …` and has rank `m a + 1`
  (`blockDatum_rank`).

### Linkage of one-term segments

- `eq_twist_one_of_singletonSegment_isLinked`: if the one-term segments `{ρ}` and
  `{σ}` are linked, then `σ = ρ.twist 1` or `ρ = σ.twist 1`. The proof takes one
  orientation of the linkage (`precedes_or_precedes`). It writes both segments in
  integral coordinates relative to `ρ` and applies the coordinate criterion
  `HasIntegralCoordinates.precedes_iff`. Its premise, the freeness of integral
  twists, is the published `Classification.cuspidalIntegralTwistFreeness`. The
  criterion forces the shift to be `1`.
- `SegmentProductDatum.ofCuspidals_isUnlinked`: if `ρ j ≠ (ρ i).twist 1` for all
  `i, j`, the multisegment of one-term segments `{ρ i}` built by
  `SegmentProductDatum.ofCuspidals` is unlinked. This is the previous lemma
  applied to each pair of its members.

### P4a: irreducibility (Bernstein and Zelevinsky 1977, Theorem 4.2)

- `PadicField.TopologicalData.isIrreducible_normalizedProductInduced_of_unlinked T B τ
  hs hirr hsc hunl`, for a block shape `B` of `t + 1` and blocks with carriers in
  `Type uW`: if `supercuspidalDatum (τ j) ≠ (supercuspidalDatum (τ i)).twist 1` for
  all `i, j`, then `T.normalizedProductInduced B τ` is irreducible.
- `Langlands.Whittaker.isIrreducible_canonicalNormalizedProductInduced_of_unlinked m
  h τ hs hirr hsc hunl`: the same for the canonical structures and the shape
  `succBlockShape m h`. The hypothesis is
  `hunl : ∀ a b, blockDatum τ hs hirr hsc a ≠ (blockDatum τ hs hirr hsc b).twist 1`.

This is Bernstein and Zelevinsky 1977, §4.2, Theorem (criterion of irreducibility).
The Lean proof derives it from the Library's proof of Zelevinsky 1980, Theorem 4.2
(`Classification.unlinkedSegmentSocleProductIrreducible`). That theorem states that
a normalized product of segment socles whose multisegment is unlinked is
irreducible. The steps are:

1. Raise each block's carrier to `Type (max uF uW)`
   (`GeneralLinear.SupercuspidalRep.universeLift`, `CuspidalDatum.universeLift`).
   Lifting is injective on data and commutes with twisting
   (`CuspidalDatum.universeLift_injective`, `CuspidalDatum.universeLift_twist`), so
   the lifted data still satisfy the hypothesis.
2. View each lifted block as the socle of its one-term segment
   (`SegmentProductDatum.ofCuspidals`, `ofCuspidals_hasSegmentSocles`). The
   multisegment is unlinked by `ofCuspidals_isUnlinked`.
3. Apply `unlinkedSegmentSocleProductIrreducible`. Then transport irreducibility
   back along `ofCuspidalsInducedIso` and the blockwise lift equivalences
   (`normalizedProductInducedEquiv`), using `Weil.IsomorphismInvariance.irreducible_iff`.

### Genericity

- `Langlands.Whittaker.isGeneric_canonicalNormalizedProductInduced ψ m h τ hirr hsc
  hprod`: if the blocks are irreducible and supercuspidal and the product is
  irreducible (`hprod`), the product satisfies `IsGeneric ψ t`. That is, it is
  irreducible and admissible and has a nonzero standard Whittaker functional. Each
  block is of Whittaker type by the supercuspidal Kirillov theorem
  (`isOfWhittakerType_of_supercuspidalKirillov supercuspidalKirillov`). The published
  `normalizedProductWhittakerType` then gives admissibility of the product and a
  linear equivalence of its space of standard Whittaker functionals with `ℂ`. The
  preimage of `1` is the nonzero functional.

### Change of carrier universe

- `Langlands.Whittaker.forall_coefficientModel_of_isGeneric ψ n Φ hΦ π hπ ℓ w`: let
  `Φ` be a property of standard Whittaker functions on `GL_(n+1)(F)`. Suppose `Φ`
  holds on every vector of every coefficient model `coefficientModel π' ℓ'` of every
  representation `π'` with carrier in `Type uV` satisfying `IsGeneric ψ n`. Then `Φ`
  holds on every vector `w` of every coefficient model of every representation `π`
  satisfying `IsGeneric ψ n`, with carrier in any universe `Type uX`. The proof takes
  an equivalent realization `σ` of `π` in `Type uV`
  (`padicIrreducibleSmoothSmallRealization`). It transfers `IsGeneric` along the
  equivalence (`isGeneric_iff_of_equiv`). The pulled-back functional
  `functionalPullback e.symm ℓ` has the same coefficient model
  (`coefficientModel_functionalPullback`).

### P4b: orthogonality

- `Langlands.Whittaker.integral_whittakerProductIntegrand_canonicalNormalizedProductInduced_eq_zero
  ψ m h τ hirr hsc hprod μ H hH ℓ w`: let `μ` be any measure on
  `LeftUnipotentQuotient t F.Carrier` (`N_(t+1) \ GL_(t+1)(F)`), for any measurable
  structure, and `H : InverseWhittakerFunctions ψ t`. Suppose `hH`:
  `∫ x, whittakerProductIntegrand ψ w'.val H x ∂μ = 0` for every vector `w'` of
  every coefficient model of every representation with carrier in `Type uV`
  satisfying `IsGeneric ψ t`. Suppose also the hypotheses of the genericity lemma.
  Then the same integral vanishes for every vector `w` of every coefficient model
  `coefficientModel Π ℓ` of the product `Π`. `hH` has the form of the last
  hypothesis of `WhittakerCompletenessStatement`; for the measure
  `unipotentQuotientHaar F.Carrier t` with the Borel structures of that statement it
  is exactly that hypothesis. The proof is the change-of-universe lemma applied to
  the genericity lemma.
- `Langlands.Whittaker.integral_whittakerProductIntegrand_eq_zero_of_unlinked`: the
  same conclusion from the hypotheses `hs`, `hirr`, `hsc` and `hunl` of P4a in place
  of `hprod`. It composes P4a and P4b.

## Provenance

The module is derived. P4a is Bernstein and Zelevinsky 1977, §4.2, Theorem, printed
page 454, which the Library's Zelevinsky 1980 Theorem 4.2 contains as the case of
one-term segments. The other declarations are internal helpers for the proof of
Jacquet and Shalika 1985, Lemma (3.2). They are derived from the published Library
results named above: linkage criteria for segments, universe lifting, normalized
induction of Whittaker type, supercuspidal Kirillov theory, small realizations and
the transport of coefficient models. The interface (the data `blockDatum` and the
split into P4a and P4b) was agreed with Worker 1810, who writes the induction.
Worker 228 wrote the module.
