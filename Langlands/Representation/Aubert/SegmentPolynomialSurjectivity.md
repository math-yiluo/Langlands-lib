# Surjectivity of the segment-polynomial evaluation

Module `Langlands.Representation.Aubert.SegmentPolynomialSurjectivity`, namespace
`Langlands.Aubert.SegmentPolynomialSurjectivity`.

The module proves that the segment-polynomial evaluation
`Langlands.Aubert.segmentPolynomialEvaluation F T hx hl` is surjective, and it
assembles bijectivity, i.e. `Langlands.Aubert.SegmentPolynomialComparisonStatement F T hx hl`
(Zelevinsky 1980, Corollary 7.5). Both results are **conditional on one hypothesis**,
the published proposition `Langlands.Classification.MultisegmentSocleExhaustion.{uF, uV} F T`
(Zelevinsky 1980, Theorem 6.1 (c)): for every `n`, every irreducible smooth
representation of `GL_n(F)` is an irreducible socle of a precedence-ordered product
of segment socles with some multisegment of degree `n`. The Library does not yet
prove this proposition.

Throughout, `F : PadicField.{uF} p`, `T : F.TopologicalData`,
`hx : BinaryProductExactnessStatement.{uF, uV} F T` and
`hl : GradedInductionRingLawsStatement F T hx` are arbitrary. Segments and
multisegments are in universe `max uF uV`. The ring structure on
`GradedGrothendieckGroup.{uF, uV} F T` is `gradedInductionRing F T hx hl`.

## Main results

- `segmentPolynomialEvaluation_surjective F T hx hl ψ hex hstep`: for a unitary
  additive character `ψ` of `F`, `hex : Classification.MultisegmentSocleExhaustion F T`
  and `hstep : HighestDerivativeLabelStep F T ψ`, the evaluation is surjective.
- `segmentPolynomialComparison_of_exhaustion F T hx hl ψ hex hstep :
  SegmentPolynomialComparisonStatement F T hx hl`.
- `highestDerivativeLabelStep F T ψ : HighestDerivativeLabelStep F T ψ`. This is
  proved, so the step is not a hypothesis of the next result.
- `segmentPolynomialComparison_of_socleExhaustion F T hx hl hex :
  SegmentPolynomialComparisonStatement F T hx hl`. Its only hypothesis is
  `hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T`. The character `ψ`
  comes from the published `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T`.

## Provenance

Zelevinsky 1980, §7, proves Corollary 7.5 from Theorem 7.1. Theorem 7.1 says: if
`⟨b⟩` occurs in `π(a) = ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩`, then `b ≤ a`, and `⟨a⟩` occurs in
`π(a)` with multiplicity one. Then 7.5 argues as follows. Group the multisegments by
cuspidal content. Within each finite group the matrix `m(b_i; b_j)` is unitriangular,
so the monomials `π(a)` form a ℤ-basis.

This module follows that structure with three internal changes.

1. **Order.** Zelevinsky orders multisegments by elementary operations on linked
   pairs (§7.1). Here we use the rank order `Multisegment.RankLE` of the published
   module `Aubert/MultisegmentRankOrder`: `RankLE b a` holds when `b` and `a` have
   equal cuspidal content and the containment count of every segment in `a` is at
   most its count in `b`. The step (*) of §7.4
   is proved there for this order (`Multisegment.RankLE.of_dropLast`), and its strict
   part is well-founded (`Multisegment.wellFounded_rankLT`). The relation between the
   two orders is neither used nor claimed.
2. **Weak labels.** Zelevinsky's `⟨a⟩` is the unique irreducible submodule of the
   precedence-ordered product (Theorem 6.1). Here `IsLabel F T b m c` means only
   that some representative of the label `c` of `GL_m` is an irreducible
   subrepresentation (`IsZelevinskySubrepresentation`) of a precedence-ordered
   product of segment socles with multisegment `b`. Neither uniqueness nor
   injectivity of `b ↦ ⟨b⟩` is used. In their place, the weighted count of all
   labels of `a` in `ζ(a)` is at most one (`labelCount_zeta_le_one`), which is the
   weak form of `m(a; a) = 1` from §7.2.
3. **Inversion.** We do not invert a unitriangular matrix. Surjectivity is proved by
   well-founded induction on the strict rank order (`basisClass_mem_evaluationRange`).

The highest-derivative input of §7.2 and §7.4 ("by 6.6 the highest derivative of
`⟨b⟩` has a submodule isomorphic to `⟨b⁻⟩`") is the proposition
`HighestDerivativeLabelStep`, a weak form of Zelevinsky 1980, 6.6. It is proved by
`highestDerivativeLabelStep`, which applies
`Langlands.Aubert.ZelevinskyHighestDerivative.exists_label_subquotient` (helper
module `Aubert/ZelevinskyHighestDerivative`) to the published homogeneity theorem
`Langlands.Classification.segmentSocleProductHomogeneity.{uF, max uF uV} F T`
(Zelevinsky 1980, Theorem 6.2). Derivatives are counted in the graded Grothendieck
group through the total derivative `gradedDerivative F T ψ` and its ring
homomorphism `gradedDerivativeRingHom F T ψ hx hl` (published module
`Aubert/GradedDerivative`). Different derivative orders land in different degrees,
so a single total derivative replaces Zelevinsky's derivative of order `λ(b)`.

Injectivity is the helper theorem
`Langlands.Aubert.segmentPolynomialEvaluation_injective_of_derivation` (helper module
`Aubert/SegmentPolynomialInjectivity`). It is applied to `gradedDerivativeRingHom` with
the published segment formulas `gradedDerivative_segmentSocle_of_length_eq_one` and
`gradedDerivative_segmentSocle_of_two_le` (Zelevinsky 1980, 3.5).

## Definitions

- `Label F T m`: the type `GeneralLinear.IrreducibleIsoClass m F.Carrier` of
  irreducible labels of `GL_m(F)` (topology `T.topology`, carriers in
  `max uF uV`).
- `basisClass F T m c`: the class of the realized irreducible `c`, placed in rank `m`
  by `gradedInclusion`.
- `coeff F T m c : GradedGrothendieckGroup F T →ₗ[ℤ] ℤ`: the coefficient of `c` in
  the rank-`m` component, read off through `factorMap`.
- `IsEffective F T x`: all coefficients of `x` are nonnegative.
- `weightedCount F T w`: the linear functional `x ↦ ∑ w m c · coeff_{m,c}(x)` of a
  weight family `w : ∀ m, Label F T m → ℤ`.
- `zeta F T hx hl a`: Zelevinsky's `ζ(a) = ∏_{Δ ∈ a} ζ(Δ)`, defined as the evaluation
  `segmentPolynomialEvaluation F T hx hl` of the monomial `(a.map MvPolynomial.X).prod`.
- `HighestDerivativeLabelStep F T ψ`: for `n > 0`, a datum
  `d : T.SegmentProductDatum n` and `π` with `d.IsZelevinskySubrepresentation π`,
  write `λ = ∑ i, (d.segments i).rank`. Then `λ ≤ n`, and there are a datum
  `d'` of degree `n - λ` and `π'` such that: `d'.multisegment` is
  `Multisegment.dropLast d.multisegment`; `d'.IsZelevinskySubrepresentation π'`; and
  `π'` is a subquotient of the order-`λ` derivative
  `(Derivative.generalLinearDerivative T ψ n λ hk).obj π`. The statement is the
  conclusion of `ZelevinskyHighestDerivative.exists_label_subquotient`, written out.
- `IsLabel F T b m c`: some irreducible `A` with class `c` is an irreducible
  subrepresentation of `d.induced` for some datum `d` with `d.multisegment = b`
  (`d.IsZelevinskySubrepresentation A`).
- `labelWeight F T b`: the indicator weight (`1` or `0`) of `IsLabel F T b`.
- `evaluationRange F T hx hl`: the range of the evaluation, as an additive subgroup.

## Lemmas

**Coefficients.** `apply_eq_sum` writes every integer-valued linear functional as the
sum of its basis values weighted by coefficients. From it: `le_of_isEffective` (two
functionals compared on basis classes compare on effective classes),
`nonneg_of_isEffective`, and `coeff_mul_le_of_isEffective` (a functional nonnegative
on basis classes dominates each weighted coefficient). Also `eq_sum_basisClass`
(every class is a finite ℤ-combination of basis classes) and `mem_of_coeff` (an
additive subgroup that contains every basis class with nonzero coefficient in `x`
contains `x`). Further: `coeff_basisClass_self`, `coeff_basisClass_of_ne`,
`isEffective_basisClass`, `isEffective_sub_basisClass`, and
`coeff_gradedInclusion_ofRepresentation` (the coefficient of an irreducible `τ` in a
finite-length representation is the composition multiplicity). The weighted-count
lemmas are `weightedCount_basisClass`, `weightedCount_nonneg`,
`coeff_mul_le_weightedCount` and `weightedCount_eq_zero_of`. The multiset lemmas are
`exists_mem_pos_of_sum_pos` and `sum_antidiagonal_eq_of_snd` /
`sum_antidiagonal_eq_of_mem_snd`: a sum over `Multiset.antidiagonal s` whose terms
vanish when the second part is nonzero equals the term at `(s, 0)`.

**Total derivative.** `isEffective_gradedDerivative_basisClass` and
`isEffective_gradedDerivative`: the derivative of an effective class is effective, by
`gradedDerivative_ofRepresentation`. `coeff_gradedDerivative_pos`: an irreducible
subquotient `B` of the order-`k` derivative of an irreducible `A` has positive
coefficient in `gradedDerivative` of the basis class of `A`. The proof uses
`compositionMultiplicity_pos_iff_isSubquotient` and bounds the order-`k` summand by
the whole sum.

**Products of segment socles.** `zeta_zero`, `zeta_add` and `zeta_singleton`
(`ζ({Δ}) = gradedSegmentSocle F T Δ`). `gradedDerivative_zeta_singleton` gives
`D ζ(Δ) = ζ({Δ}⁻) + ζ(Δ)`, from the published segment formulas.
`gradedDerivative_zeta` is the Leibniz formula
`D ζ(a) = ∑_{(a₁, a₂) ∈ antidiagonal a} ζ(a₁⁻ + a₂)`, where `a⁻ = Multisegment.dropLast a`.
It follows from multiplicativity of `gradedDerivativeRingHom` and
`Multiset.prod_map_add`. `exists_datum` realizes every multisegment as
`d.multisegment` for a datum with segment socles, using
`SegmentProductDatum.exists_of_list` and the published
`Classification.segmentZelevinskyConstituentExistence`. `zeta_multisegment`
identifies `ζ(d.multisegment)` with the class of `d.induced`; this is the helper
theorem `gradedInclusion_induced_eq_segmentPolynomialEvaluation` (helper module
`Aubert/SegmentProductClass`). Consequences: `isEffective_zeta`,
`coeff_zeta_eq_zero_of_ne` (ζ(a) lives in degree `a.degree`), and
`isSubquotient_of_coeff_zeta_pos`.

**Supports.** `classSupport_of_isSubquotient`: every irreducible subquotient of
`d.induced` has supercuspidal support (`SupportGrading.classSupport`) equal to
`d.multisegment.cuspidalContent`. The proof uses
`SegmentProductCuspidalEmbedding.embedsCuspidal_induced`,
`SupportGrading.supercuspidalSupport_eq` and
`SegmentHeadSupport.isSubquotient_trans`. `classSupport_of_coeff_zeta_pos` is the
same for constituents of `ζ(e)`.

**Multisegment bookkeeping.** `degree_multisegment`, `eq_zero_of_degree_eq_zero`,
`sum_rank_pos`, `degree_dropLast_lt` (`a ≠ 0 → deg a⁻ < deg a`), and
`card_cuspidalContent_dropLast` (`|content(b⁻)| + |b| = |content(b)|`).

**Labels.** `IsLabel.degree` (`b.degree = m`) and `IsLabel.classSupport`
(the support of `c` is `b.cuspidalContent`). `exists_isLabel hex` says that every
label is a label of some multisegment; this is the only use of exhaustion.
`gradedUnit_eq_basisClass`: the unit is the basis class of the irreducible rank-zero
representation `T.binaryProductUnit`. `exists_derivative_isLabel hstep`: a label `c`
of `b` in degree `m > 0` yields `k` with `0 < k ≤ m` and a label `c''` of `b⁻` in
degree `m - k` with positive coefficient in `gradedDerivative` of the basis class of
`c` (by `hstep` and `coeff_gradedDerivative_pos`).

## Proofs

**`one_le_coeff_zeta_of_isLabel`.** A label of `b` occurs in `ζ(b)`: it is a
subrepresentation of `d.induced`, so its composition multiplicity is positive.

**`rankLE_of_coeff_zeta_pos hstep` (rank-order form of Theorem 7.1, §7.4).** If `c`
is a label of `b` and `coeff_c ζ(a) > 0`, then `RankLE b a`. Use strong induction on
the degree `m`. The cuspidal contents of `b` and `a` agree, since both equal the
support of `c`. If `m = 0`, then `a = b = 0`. If `m > 0`, take `k` and `c''` from
`exists_derivative_isLabel`. Since `ζ(a)` is effective and `gradedDerivative` is
effective on basis classes, `coeff_mul_le_of_isEffective` gives
`coeff_{c''} (D ζ(a)) ≥ coeff_c ζ(a) · coeff_{c''} (D [c]) > 0`. By
`gradedDerivative_zeta`, some term `ζ(q₁⁻ + q₂)` with `q₁ + q₂ = a` has
`coeff_{c''} > 0`. The induction hypothesis in degree `m - k` gives
`RankLE b⁻ (q₂ + q₁⁻)`. Then `Multisegment.RankLE.of_dropLast` gives `RankLE b a`.

**`labelCount_zeta_le_one hstep` (weak form of §7.2).**
`weightedCount (labelWeight a) (ζ(a)) ≤ 1`. Use strong induction on `a.degree`. For
`a = 0`, `ζ(0)` is the unit, which is a single basis class. For `a ≠ 0`, every basis
class `[c]` satisfies `labelWeight a c ≤ weightedCount (labelWeight a⁻) (D [c])`: by
`exists_derivative_isLabel`, a label of `a` has a label of `a⁻` in its derivative.
By `le_of_isEffective` applied to `ζ(a)`, the label count of `a` in `ζ(a)` is at
most the label count of `a⁻` in `D ζ(a)`, which is a sum over the antidiagonal by
the Leibniz formula. If `q₂ ≠ 0`, the term `ζ(q₁⁻ + q₂)` contributes zero
(`labelCount_zeta_eq_zero`). A label of `a⁻ = q₁⁻ + q₂⁻` occurring there would give
`content(q₂⁻) = content(q₂)`, and then `card_cuspidalContent_dropLast` forces
`q₂ = 0`. `sum_antidiagonal_eq_of_mem_snd` leaves the label count of `a⁻` in
`ζ(a⁻)`. This is at most one by induction, because `deg a⁻ < deg a`.

**`basisClass_mem_evaluationRange hex hstep`.** Every basis class lies in the range.
By `exists_isLabel`, `c` is a label of some `b`. Use well-founded induction on `b`
for the strict rank order `wellFounded_rankLT`. Let `y = ζ(b) - [c]`. It is
effective, by `one_le_coeff_zeta_of_isLabel` and `isEffective_sub_basisClass`. Its
label count for `b` is at most `0`, by `labelCount_zeta_le_one`. Every basis class
`[c']` with nonzero coefficient in `y` is a constituent of `ζ(b)`. It is a label of
some `b'` (`exists_isLabel`), with `RankLE b' b` (`rankLE_of_coeff_zeta_pos`) and
`b' ≠ b` (else `y` would have positive label count for `b`). So `[c']` is in the
range by the induction hypothesis. Then `y` is in the range by `mem_of_coeff`, and
`[c] = ζ(b) - y` is in the range.

**`segmentPolynomialEvaluation_surjective`.** Every class is a ℤ-combination of
basis classes (`mem_of_coeff`), and every basis class is in the range.

**`segmentPolynomialComparison_of_exhaustion`.** Injectivity comes from
`segmentPolynomialEvaluation_injective_of_derivation` with
`D = gradedDerivativeRingHom F T ψ hx hl`, whose segment hypotheses are
`gradedDerivative_segmentSocle_of_length_eq_one` and
`gradedDerivative_segmentSocle_of_two_le`. Surjectivity comes from the previous
theorem.

**`highestDerivativeLabelStep`.** This is
`ZelevinskyHighestDerivative.exists_label_subquotient F T
(Classification.segmentSocleProductHomogeneity.{uF, max uF uV} F T) ψ`. Its conclusion
is the body of `HighestDerivativeLabelStep`.

**`segmentPolynomialComparison_of_socleExhaustion`.** Obtain `ψ` from
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T`, then apply
`segmentPolynomialComparison_of_exhaustion` with `highestDerivativeLabelStep F T ψ`.

## Helper modules

The module imports three helper modules by Worker 237, included unchanged:
`Aubert/SegmentProductClass` (`zeta_multisegment`, `hasFiniteLength_induced`),
`Aubert/SegmentPolynomialInjectivity` (injectivity) and
`Aubert/ZelevinskyHighestDerivative` (the label step).
