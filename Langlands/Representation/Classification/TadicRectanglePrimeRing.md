# The ring `R` in segment-monomial coordinates (helper for Tadić's Proposition 3.8)

Author: Worker 4021. Module
`Langlands.Representation.Classification.TadicRectanglePrimeRing`, namespace
`Langlands.Classification.TadicRectanglePrime`. It is a helper module of the proof
`Langlands.Classification.TadicRectanglePrime.tadicRectangleSoclePrime` of
`Langlands.Classification.TadicRectangleSoclePrime`. It adds no hypothesis and uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`. Every result is stated for
arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, `T : F.TopologicalData`.

## Provenance

The module translates three facts from A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II*, Ann. Sci. ÉNS (4) 13 (1980), literature ID
`zelevinsky-1980-induced-ii`, into the coordinates used by Tadić in the proof of his
Proposition 3.8 (`tadic-1986-unitary`, §3.3 and §3.5, printed pp.353–354, PDF pp.20–21):

- Corollary 7.5: `R` is the polynomial ring over `ℤ` in the classes `ζ(Δ)` of the
  segments (Library: `Aubert.segmentPolynomialEquiv` with the published comparison
  `Aubert.segmentPolynomialComparison`).
- Theorem 7.1: `ζ(a) = ∑_{b ≼ a} m(b; a) ⟨b⟩` with `m(a; a) = 1`. Tadić §3.5 inverts this
  unitriangular system to write `⟨a⟩ = ∑_{b ≼ a} m'_{b,a} ζ(b)` with `m'_{a,a} = 1`.
  `poly_basisClass` below is this inversion. The order is the Library's rank order
  `Multisegment.RankLE` (equal cuspidal content and containment counts of `b` at least
  those of `a`), in which the Library proves Theorem 7.1
  (`Aubert.SegmentPolynomialSurjectivity.rankLE_of_coeff_zeta_pos`,
  `labelCount_zeta_le_one`).
- Proposition 4.6: for `Δ` preceding `Γ`, `ζ(Δ ∪ Γ) ζ(Δ ∩ Γ)` is a subquotient of
  `ζ(Γ) ζ(Δ)` (Library: `linkedSegmentSocleReverseProductStructure`). Tadić uses it in
  §3.6–3.7 to see that the neighbours `a_{k,k+1}` occur in `ζ(a₀)`.

## Definitions

- `ringR`: the ring structure `Aubert.gradedInductionRing F T (binaryProductExactness F T)
  (gradedInductionRingLaws F T _)` on `Aubert.GradedGrothendieckGroup F T`, the ring of
  the target statement. It is a local instance in the helper modules.
- `ψ₀`: a unitary additive character chosen from
  `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`; it only serves to call the
  published triangularity theorems, which take one as a parameter.
- `zetaR a`: the published `Aubert.SegmentPolynomialSurjectivity.zeta` of `a` for this ring.
- `segmentEquiv`: the ring isomorphism `ℤ[segments] ≃+* R` of Corollary 7.5, sending
  `X_Δ` to `ζ(Δ)`.
- `poly x`: the polynomial `segmentEquiv⁻¹ x` of a class `x`.
- `polyCoeff μ`: the `ℤ`-linear functional `x ↦ (poly x).coeff μ` (`polyCoeff_apply`).

## Results

### Monomials

- `prod_map_X_eq_monomial`: `∏_{S ∈ s} X_S = X^{toFinsupp s}` for a multiset `s`.
- `poly_zetaR`: `poly (ζ(b))` is the monomial `X^b` (Mathlib's
  `Multiset.toFinsupp b` with coefficient `1`), because `ζ(b)` is by definition the
  evaluation of `∏_{Δ ∈ b} X_Δ`.

### Effective classes

`IsEffective x` (Library) means that every coefficient of `x` in the basis of
irreducible classes is `≥ 0`.

- `basisSpan`, `mem_basisSpan_of_isEffective`: an effective class is a sum of basis
  classes (`eq_sum_basisClass`, with nonnegative coefficients turned into natural
  multiples).
- `isEffective_basisClass_mul`: the product of two basis classes `[A] [B]` is the class
  of the actual normalized product `A × B` (`gradedMultiplication_homogeneous`,
  `binaryProductK0_classes`), hence effective.
- `isEffective_mul`: products of effective classes are effective, by closure induction
  on both factors in `basisSpan`.
- `coeff_le_of_isEffective_sub`: if `y - x` is effective, coefficients of `x` are at
  most those of `y`.
- `apply_eq_of_coeff`: two `ℤ`-linear functionals that agree on every basis class
  occurring in `x` agree on `x` (`apply_eq_sum`).

### Labels

`IsLabel b m c` (Library) means that `c` is the class of an irreducible
subrepresentation of a product of segment socles with multisegment `b`.

- `rankLE_of_isLabel_of_coeff_pos`: a label of `b` occurring in `ζ(a)` gives `b ≼ a`
  (Theorem 7.1, `rankLE_of_coeff_zeta_pos`).
- `coeff_zetaR_pos_of_isLabel`: a label of `a` occurs in `ζ(a)`.
- `eq_of_isLabel`: a class that is a label of `a` and of `b` forces `a = b` (both
  `a ≼ b` and `b ≼ a`, and `RankLE.antisymm`).
- `isEffective_zetaR_sub_basisClass`: for a label `c` of `a`, `ζ(a) - [c]` is effective.
- `coeff_zetaR_sub_basisClass_eq_zero`: for labels `c, c'` of `a`, the coefficient of
  `c'` in `ζ(a) - [c]` is `0`. The labels of `a` occur in `ζ(a)` with total multiplicity
  at most one (`labelCount_zeta_le_one`), and `c` already uses it.

### `poly_basisClass` (Theorem 7.1 in the monomial basis)

For every label `c` of `b`: the coefficient of `X^b` in `poly [c]` is `1`, and every
monomial `X^μ` with nonzero coefficient satisfies `toMultiset μ ≼ b`.

Proof: well-founded induction on `b` for the strict rank order
(`Multisegment.wellFounded_rankLT`). Put `y = ζ(b) - [c]`, which is effective. Let `c'` be
a basis class with nonzero coefficient in `y`. By exhaustion (`exists_isLabel` with the
published `multisegmentSocleExhaustion`) `c'` is a label of some `b'`. The coefficient of
`c'` in `ζ(b)` is positive, because that of `[c]` is `≥ 0`. So `b' ≼ b`. Moreover
`b' ≠ b` by `coeff_zetaR_sub_basisClass_eq_zero`. The induction hypothesis for `b'`
puts every monomial of `poly [c']` in the set `{μ | toMultiset μ ≼ b, toMultiset μ ≠ b}`
(transitivity, and antisymmetry for `≠`). The polynomials supported there form an
additive subgroup (Mathlib's `MvPolynomial.restrictSupport`), whose preimage in `R`
contains `y` by the Library's `mem_of_coeff`. Finally `poly [c] = X^b - poly y`, and
`poly y` has no monomial `X^b`.

### `exists_isEffective_zetaR_pair_sub` (Proposition 4.6 in `R`)

If `Δ` precedes `Γ`, there are `U` and an optional `I` with
`Γ.IsUnionIntersectionReplacement Δ U I` (supports of `U` and `I` are the union and the
intersection; `I = none` when the intersection is empty) and
`ζ({Γ, Δ}) - ζ(U :: I)` effective.

Proof: `SegmentProductDatum.exists_of_list` with the published
`segmentZelevinskyConstituentExistence` gives a product datum `d` with segments
`[Γ, Δ]` and segment-socle blocks. The published `linkedSegmentSocleReverseProductStructure`
gives `U`, `I`, and a product datum `e` with segments `U :: I`, segment-socle blocks and
irreducible `e.induced`, which is equivalent to the graded piece of index `1` of a
two-step filtration of `d.induced`. So `e.induced` is a subquotient of `d.induced`
(`DistinctCuspidalProduct.exists_isSubquotient_graded`), its composition multiplicity is
positive, and its coefficient in `[d.induced] = ζ({Γ, Δ})` (`zeta_multisegment`) is at
least `1`. Since `ζ(U :: I) = [e.induced]` is a basis class, `isEffective_sub_basisClass`
concludes.
