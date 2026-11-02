# Norms of normalized Jacquet exponents of weak segment special quotients

Author: Worker 561. The proof uses the published all-shape factor theorem of
Workers 485 and 1039 and the published scalar and central-character results;
their original modules retain their attribution. The local norm reduction and
interval transport calculations are Worker 561's.

## Declaration and scope

`Langlands.Classification.segmentSpecialJacquetExponentNormFormula` proves the
unchanged proposition `SegmentSpecialJacquetExponentNormFormula` in
`SegmentSpecialJacquetExponentStatement`. Its only parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The universes `uF` and `uV` are independent, with the statement's actual
representation carriers in `Type (max uF uV)`.

The input constituent hypothesis is the weak `T.IsSegmentQuotient Δ π`.
The base representative and its scalar character `ω` are arbitrary supplied
data. For every ordered standard block shape and every generalized
Jacquet eigencharacter, the conclusion supplies positive interval lengths,
rank-divisible block sizes, their total sum and exactly the stated product
norm, with both scalar and absolute-value factors inside each product term.

## Implemented proof

Apply the published `segmentQuotientJacquetFactors` to the supplied weak
quotient and actual block shape. Its subsingleton branch is impossible:
a generalized eigencharacter provides a nonzero vector of the actual
Jacquet module. Its tensor branch supplies positive lengths `k i`, the
block ranks and total sum, successive descending subsegments, weak quotients
on the actual block groups and an actual equivalence of normalized Jacquet
representations with their tensor product.

Write `m = Δ.length`, `r = Δ.rank` and
`K i = ∑ j : Fin B.length with j < i, k j`. The published
`prefix_add_le_sum` gives `K i + k i ≤ m`. The private interval calculation
chooses the representative obtained by twisting the supplied `A` by
`ν^(m - K i - k i)`. The supplied equality representing `Δ.base` transports
to the twisted base. `hasScalarCharacter_twist` computes that
representative's scalar character. The weak-quotient conjunct of the
published `segmentConstituentCentralCharacter` computes the interval
quotient's scalar character. `prod_twistedScalarCharacter` and the identity

```
m - 1 - (K + j) = (m - K - k) + (k - 1 - j)
```

for `j < k` rewrite it as the product of the original descending scalar
characters on that interval. The bound `K + k ≤ m` justifies the natural
subtractions. This uses no uniqueness or real-part witness for `ω`.

Two private wrappers eliminate the supplied segment base/length equalities
and the actual rank equality. They transfer the computed scalar character
to the factor representation on `GL_(B.size i)` itself.

The published `hasScalarCharacter_blockTensor_splitCentre` gives the product
of the coordinate scalar characters on the whole tensor. Pulling it back
through the injective intertwiner underlying the Jacquet equivalence gives
that scalar action on the original Jacquet representation. The published
`scalar_generalized_character_eq` therefore identifies every generalized
eigencharacter with this character; it does not require a composition series
or restrict to ordinary eigenvectors. Finally,
`norm_prod_blockDescendingIntervalScalarCharacter` evaluates the norm. Its
finite interval sum is

```
∑ j < k, (m - 1 - (K + j)) = k * ((2*m - k - 1)/2 - K)
```

in `ℝ`; multiplication by the cuspidal rank gives exactly the target's
exponent. The positive interval lengths and ordered prefix sums supplied by
the factor theorem are retained unchanged.

## Published inputs and provenance

The all-shape input is
`Classification.segmentQuotientJacquetFactors`, proved in
`Classification.SegmentQuotientJacquetFactorsProof` by Workers 485 and 1039.
It independently supplies the weak-quotient upgrade, proper two-block
vanishing and tensor formula, and normalized ordered transitivity; the
present proof does not take any of them as a hypothesis.

The central-character input is
`Classification.segmentConstituentCentralCharacter` in
`Classification.SegmentConstituentCentralCharacterProof`. Scalar detection
is imported from `Exponents.ScalarGeneralizedEigencharacterProof` and interval
arithmetic and tensor scalar action from
`Exponents.DescendingIntervalBlockScalarProof`. Only the private shifted
interval, equality transport and final norm assembly are new here.

This complete all-shape generalized-character norm formula is derived
algebra, rather than a verbatim quotation. Its original source inputs are
Zelevinsky 1980, *Induced representations of reductive p-adic groups II*,
registered as `zelevinsky-1980-induced-ii`: section 9.1 and its descending
full-Jacquet tensor (printed p.197, PDF p.34), Proposition 9.5 and its
terminal-first two-block formula (printed p.198, PDF p.35), and the referenced
route in section 3.4 (printed pp.181–182, PDF pp.18–19). The imported
all-shape proof derives the passage to arbitrary ordered shapes using
actual Jacquet transitivity. The original passages and current source-boundary
notes were read in this branch. The Library uses upper block parabolics,
positive half-modulus normalized induction with right translation, and the
inverse half-modulus normalized Jacquet action. All inputs use these actual
constructions.

No analytic hypothesis or conclusion is added. In particular, the weak
quotient need not be supplied as a strong head, and no unitary, square-integrable
or finite-length hypothesis is imposed on it or on `ω`. Dependency audit
and exact-target validation are recorded separately during submission.

## Dependency and independence audit

The author's source audit uses Library commit
`159d1197aca62e7ba065e111be014f24f26d0387`. Every inherited Lean/Markdown
pair in this proof's project import closure agrees with that Library.
The dependencies of the published all-shape factor proof are unchanged from
its independent review base, and the previously audited full-Jacquet closure
is unchanged. The norm entry is the only new module; it imports the published
factor, central-character, scalar-detection and interval-scalar proofs by
their Lean names. The target pair and its dependencies are unchanged.

The closure excludes forward special square-integrability
(`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`), parent ordered conversion
(`8252833d-c269-41a9-824c-5879e531b23b`), square-integrable exhaustion
(`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), regular exhaustion
(`bf433f0a-921a-428c-b0c0-6475438125ac`), square-integrable Langlands
classification (`1cb45da2-7007-4351-a694-594fb148b8d1`), strong-head
analytic classification (`aca8805b-054f-4d56-8045-12db7f623404`),
tempered block uniqueness (`52e97845-36bb-457d-b76f-70753334b88c`),
multisegment exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`),
ordered-head existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), and
quotient coverage (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`). The inherited
additional exclusions on segment-head product irreducibility, generic
segment-product uniqueness, segment-socle exhaustion and segment derivative
formulas are also retained. No proof uses Zelevinsky 1980 section 9.3 or
9.17 as an input.

The upstream proof of `twoSupercuspidalNonadjacentProductIrreducible` uses the
fully proved general Bernstein–Zelevinsky 1977 derivative theory, including
Gelfand–Kazhdan realization and the general Leibniz rule. This is the route
expressly allowed by the operator's answer to the source-boundary question;
it uses independently accepted Library proofs, rather than assuming a
derivative theorem. All derivative, mirabolic, Whittaker and Gelfand–Kazhdan
modules in the present closure belong to that general upstream closure.
That closure contains neither the present norm target nor the later
full/head/socle Jacquet conclusions, segment derivative formulas,
highest-derivative support shift, the segment-socle part of cuspidal
derivatives, or the excluded classification results. In particular, the
upstream general route does not use Zelevinsky 1980 sections 3.5 or 9.6.
The present module adds no derivative theorem.

The original frozen central-character and interval-scalar submissions have
small integration changes. The former replaces a redundant local
`leviModulus_scalarLevi` helper with the identical published
`leviModulus_scalar`; its final theorem is unchanged. The latter replaces
a private determinant scalar-norm calculation with the published
`norm_determinantPowerCharacter_scalar`. Both integration diffs were read,
and the current published sources are the sources used here. The audit
does not assert byte identity between these two frozen submissions and
their integrated versions.

This is an author dependency and provenance audit, supplementing the
independent reviews of the imported results. Compilation and this audit
do not constitute independent acceptance of the norm proof.
