# Shahidi's Theorem 5.1: the local coefficient is a JPSS gamma factor

This module states Theorem 5.1 of F. Shahidi, *Fourier transforms of
intertwining operators and Plancherel measures for GL(n)*, American Journal of
Mathematics 106 (1984), 67–111, printed page 103. The statement includes the
measure normalization of pages 75–77. The main declaration is the Prop-valued
definition `Langlands.Shahidi.LocalCoefficientGammaStatement`. The theorem is
neither proved nor assumed; its proof remains a separate obligation. The module
also defines the representation-independent part of the pages 75–77 normalization,
`IsEqualRankGeometricNormalized`, and proves how it relates to the published
full normalization.

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`. The
passages used are printed pages 68, 70–73, 75–80, 94–96 and 102–104. The author
is Worker 11. This revision replaces candidate `f4aaa918`, which Reviewer 1599
rejected because its measures were not linked to the pages 75–77 normalization.

## The source statement

Page 103:

> THEOREM 5.1. Let `π₁` and `π₂` be two irreducible admissible non-degenerate
> representations of `G_m` and `G_n`, respectively. Then there exists a
> normalization of measures defining `C_χ(s, π₁ ⊗ π₂)` such that
>
> (5.2) `C_χ(s, π₁ ⊗ π₂) = ω₂^m(−1) ε'(s, π₁ × π̃₂, ψ)`.

The notation comes from the following places.

- Page 70, Section 0: `F` is a non-archimedean local field with ring of
  integers `O`, and `G_r = GL_r(F)`. "Let `ψ` be a non-trivial additive
  character of `F`. We assume that the largest ideal of `F` on which `ψ` is
  trivial is `O`." The character `χ` of the upper unipotent subgroup `N_r` is
  `χ(n) = ψ(n₁₂ + ⋯ + n_{r−1,r})`. A representation is non-degenerate if it
  has a nonzero linear functional `λ` with `λ(π(n)v) = χ(n)λ(v)`.
- Pages 72–73: `C_χ(s, π)` for `π = π₁ ⊗ π₂` is defined by
  `λ^{−s}_{π'}(A(s, π, w_{m,n}) f) = C_χ(s, π)^{−1} λ^s_π(f)` (0.3). Page 73
  remarks that `C_χ(s, π)` depends on the measures that define
  `A(s, π, w_{m,n})`, `λ^s_π` and `λ^{−s}_{π'}`.
- Page 102, Section 5: `ω₂ = π₂|Z_n`, the central character of `π₂`.
- Page 68: `ε'(s, π₁ × π₂, ψ) = ε(s, π₁ × π₂, ψ) L(1 − s, π̃₁ × π̃₂) / L(s, π₁ × π₂)`.
  This is the JPSS gamma factor `γ(s, π₁ × π₂, ψ)`, not the raw epsilon
  factor. Page 68 also states the theorem in this form.

## The normalization of measures in the source

Pages 75–77 fix the measures in the equal-rank case `G_n × G_n`, in seven
items:

1. Item 1 (pages 75–76) uses the Hermitian pairing of Lemma 1.1 on the space of
   `π₂` and Proposition 1.2. With arbitrary `dn₁` on `N_{n−1}` and `dn₂` on
   `U_n ≅ F^{n−1}`, the pairing fixes the quotient measure `dȧ` on
   `N_{n−1}\G_{n−1}`, and `d*a` is the composite of `dȧ` and `dn₁`. Page 76
   observes that `d*a·dn₂` does not depend on `dn₁` or `dn₂`.
2. `d*z` on the centre is fixed by `∫_{K_{n−1}×O^{n−1}×O*} d*a dn₂ d*z = 1`,
   and `dz = |z| d*z`.
3. `dx₁ ⋯ dx_n` is self-dual on `F^n`, with `dx₁ = dz`. The measure `dk` on
   `K_n` is fixed by `∫_{K̃_{n,m}} dk = dx₂(P^m) ⋯ dx_n(P^m)`.
4. `d*g = |det a|^{−1} dn₂ d*a d*z dk` on `G_n` (Iwasawa decomposition), and
   `∫_K d*g = ∫_K dk`.
5. `da = |det a|^n d*g` on `M_n`, written as `∏ da_ij` with `da_11 = dx₁ = dz`
   and `da_i1 = dx_i`.
6. The measure on `V` is arbitrary, but the same for `λ^s_π` and `λ^{−s}_{π'}`
   after replacing `f` by `R_{w₀^{−1}} f`.
7. The measure on `U` is `du = da`.

Only item 1 uses a representation, through its Hermitian pairing, and so needs a
unitary `π₂`. Items 2–7 are geometric. Once `d*a·dn₂` is fixed, they fix the
intertwining measure `du = da` of (0.3), and item 1 fixes `d*a·dn₂`. The measure
on `V` stays arbitrary (item 6), but both Jacquet functionals use it, so its scale
cancels in (0.3) and does not affect `C_χ`.

Pages 78–80 do not change these measures. For `m ≠ n` the source gives no general
recipe. Section 4 (pages 94–96) fixes the measures for `G_{n−1} × G_n` for its
Proposition 4.2 (unitary supercuspidal representations). There `db = db'` and
`dX' = dY` are "otherwise free", and items 2–7 are analogues of the ones above.
The proof of Theorem 5.1 (pages 103–104) reduces to supercuspidal pairs through the
multiplicativity of `C_χ` ([19], Theorem 3.2.1) and of `ε'` ([11], Theorem 3.1).
The supercuspidal cases (Lemma 5.1, Propositions 3.1 and 4.2) each again assert that
some normalization exists.

## The geometric normalization

`IsEqualRankGeometricNormalized ψ abv d` is a predicate on the published
`EqualRankMeasureData O n` (module `EqualRankMeasures`) for the ranks `n + 1`. It
is the conjunction of the published conditions for the geometric items, applied
to the actual measures of `d`:

- `IsEqualRankHaarData d`: the Haar and regularity conditions;
- the geometric relations of item 1: `IsUnipotentProductMeasure d.dn₁ d.dn₂ d.dn`
  (`dn = dn₁ dn₂`), `IsQuotientReflectionRelated` (the two quotient measures of
  Lemma 1.1 and Proposition 1.2 correspond under the published reflection), and
  `IsSmallerQuotientCompatible d` (the quotient measure composed with `dn₁` is
  `d*a`, through the Weil integration formula);
- `IsCompactVolumeCompatible`: the compact volumes of items 2 and 3;
- `IsIwasawaMeasureCompatible`: item 4;
- `IsCoordinateMeasureCompatible n abv ψ`: the coordinate conditions of items 2,
  3 and 5. These are `dx₁ = |z| d*z`, the self-duality of `dx₁ ⋯ dx_n` for the
  page-76 transform with `ψ̄`, `da = |det a|^n d*g`, and `da_i1 = dx_i`;
- `IsEqualRankRadicalMeasureCompatible`: items 6 and 7, with the actual radical
  pushforwards.

Only the nonzero functional and the two pairing equations of item 1 are left out.
`isEqualRankMeasureNormalized_iff` proves that the published full normalization
`IsEqualRankMeasureNormalized ψ π b ℓ abv d` holds exactly when
`IsEqualRankGeometricNormalized ψ abv d` holds, `ℓ ≠ 0`,
`IsWhittakerPairingNormalized ψ n π b ℓ d.dn` holds, and
`IsKirillovPairingNormalized ψ n π ℓ b d.primedQuotient` holds. So no condition is
weakened or added. The lemma `IsEqualRankMeasureNormalized.geometric` is the
forward direction. `IsEqualRankGeometricNormalized.radical_coordinates` extracts
`d.intertwining = matrixCoordinateMeasure d.da` (items 5 and 7) and
`d.jacquet = d.swappedJacquet` (item 6).

In the equal-rank case these coordinates are the ones of the published
local-coefficient relation. `d.intertwining` is the coordinate measure of the
radical `U`, which `intertwiningUnipotent = upper` parametrizes at equal ranks. The
Jacquet integrands of `JacquetIntegral` evaluate `f` at `lower(a) · w` (published
`jacquetIntegrand_lower`) and at `w⁻¹ · upper(a)`. At equal ranks the block Weyl
element is an involution (`blockWeyl_mul_self_equalRanks`, proved here), and
`w⁻¹ · upper(a) = lower(a) · w⁻¹` (`blockWeyl_inv_mul_upper_equalRanks`, proved
here). So both integrals are page 78's integrals over the lower radical `V` in the
same coordinates `a`, after `f ↦ R_{w₀^{−1}} f`. Hence `d.jacquet` and
`d.swappedJacquet` are the two measures of item 6.

## The Lean statement

`LocalCoefficientGammaStatement` (universes `uF` of the field and `uV` of the
representation spaces) says the following. Write `T` for
`F.canonicalTopologicalData`, the Library's realization of a p-adic field.
`F.Carrier` carries `T.topology` and the Borel measurable structure.

For every prime `p` and every `F : PadicField p`, take:

- `ψ`, a unitary additive character of `F.Carrier`. The Library's additive
  characters are nontrivial.
- `ν : SelfDualHaar T ψ`, an additive Haar measure on `F` that is self-dual for
  `ψ` under the Library's plus-sign Fourier transform.
- the hypothesis `T.additiveConductor ψ = 0`. This is the page-70 assumption that
  `O` is the largest ideal on which `ψ` is trivial. The published
  `additiveConductor ψ` is Tate's `n(ψ)`, the largest `n` with
  `ψ(ϖ^{−n} O) = 1`. The published `HighlyRamifiedGammaStabilityStatement`
  encodes the same convention the same way.

Then two statements hold.

**All positive ranks.** Let `m n : ℕ`, and let `π₁`, `π₂` be complex
representations of `GL_{m+1}(F)` and `GL_{n+1}(F)` on complex vector spaces `V₁`,
`V₂` in one universe. Assume `Whittaker.IsGeneric ψ m π₁` and
`Whittaker.IsGeneric ψ n π₂`. Let `ω : F.Carrierˣ →* ℂˣ` satisfy
`Classification.HasGLCentralCharacter F.Carrier (n + 1) π₂ ω`. Then there exist
additive Haar measures `ν_I`, `ν_J` on `F` with

`IsLocalCoefficientGammaComparison F ψ ν π₁ π₂ ω (rectangularMeasure ν_I (n+1) (m+1))
(rectangularMeasure ν_J (n+1) (m+1)) (rectangularMeasure ν_J (m+1) (n+1))`.

**Equal ranks at least two.** Let `n : ℕ` with `0 < n`, and let `π₁`, `π₂` be
representations of `GL_{n+1}(F)` with the same hypotheses, and `ω` as before.
Then there is
`d : EqualRankMeasureData T.Integers n` with

`IsEqualRankGeometricNormalized ψ T.shahidiAbsoluteValue d` and
`IsLocalCoefficientGammaComparison F ψ ν π₁ π₂ ω d.intertwining d.jacquet d.swappedJacquet`.

In the equal-rank statement, the measurable structures on `Fˣ`, `GL_n(F)`,
`GL_{n+1}(F)`, the two upper unipotent groups, the quotient
`KirillovQuotient n F`, the integral subgroup `GL_{n+1}(O)` and
`GL_{2n+2}(F)` are the Borel σ-algebras of their canonical topologies. The ring
`O` is the integer ring `T.Integers`, and `abv` is `T.shahidiAbsoluteValue`, the
normalized absolute value (`|ϖ| = q^{−1}`), which is also used by the induced
spaces.

`IsLocalCoefficientGammaComparison F ψ ν π₁ π₂ ω μ μJ μJ'` says that there are
`C`, `G : RatFunc ℂ` such that the following three statements hold.

1. `T.IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C`. Here `μ` is the measure
   `du'` of the intertwining integral (0.1) on the `(n+1) × (m+1)` coordinates of
   `U'`. `μJ` is the measure of the Jacquet functional `λ^s_π` (0.2), and `μJ'` is
   the measure of `λ^{−s}_{π'}`. The relation (published in
   `LocalCoefficientPadic`) says that `π₁` and `π₂` have nonzero standard
   Whittaker functionals. It also says that for all nonzero ones `λ₁`, `λ₂`,
   equation (0.3) holds with `C_χ(s, π) = C(q^{−s})` for `Re s` large, on the
   actual p-adic induced space `I(s, π₁ ⊗ π₂)`, with the stabilized Jacquet
   integrals. Here `q` is the residue cardinality. The inverse convention
   `C^{−1}` of (0.3) is kept.
2. `IsPadicSymmetricGammaFactor F ψ ν π₁ (smoothContragredient π₂) G`, that is,
   `γ(s, π₁ × π̃₂, ψ) = G(q^{−s})`. Here `π̃₂` is the published smooth
   contragredient of `π₂` and `ν` is the self-dual measure.
3. `C = ω(−1)^{m+1} • G`. The scalar action of `ℂ` on `RatFunc ℂ` is
   multiplication by a constant. So this is
   `C_χ(s, π₁ ⊗ π₂) = ω₂(−1)^{m+1} γ(s, π₁ × π̃₂, ψ)`. This is (5.2): the
   source's `ω₂^m(−1)`, with the rank of `π₁` equal to `m + 1`.

Notes on the hypotheses:

- The source's ranks `m` and `n` are our `m + 1` and `n + 1`, so all positive
  ranks are covered. One universe for `V₁` and `V₂` is needed because the
  induced space uses the published two-factor tensor product.
- The published `IsGeneric` means irreducible, admissible (which includes
  smooth), and having a nonzero functional for the standard character
  `u ↦ ψ(Σᵢ u_{i,i+1})`. This is the source's "irreducible admissible
  non-degenerate".
- `HasGLCentralCharacter` says that every scalar matrix `c · 1` acts on `V₂` by
  `ω(c)`, i.e. `ω = ω₂ = π₂|Z_n`. Such an `ω` exists, by the published
  `admissibleSchur_centralCharacter` restricted to scalar matrices. It is unique
  because `π₂ ≠ 0`. So the hypothesis is not vacuous and `ω(−1)` is determined by
  `π₂`. These are remarks; this module does not prove them.
- No unitarity or supercuspidality hypothesis is imposed.

`C` and `G` are unique when they exist, by the published
`IsShahidiLocalCoefficient.unique` (`π₁` and `π₂` are smooth) and
`IsPadicSymmetricGammaFactor.unique`. The source takes both for granted: `C_χ`
exists by multiplicity one of Whittaker functionals for the induced representation
(page 68, citing [19]), and `ε'` exists by [8, 11].

## How the normalization enters, and its provenance

**Equal ranks: pages 75–77.** The measures of (0.3) are literally
`d.intertwining`, `d.jacquet` and `d.swappedJacquet` of a datum with the geometric
normalization. So the intertwining measure is the matrix-coordinate measure `da`
of item 5, coupled through items 2–5 to the central, coordinate, compact and
Iwasawa measures. The two Jacquet measures are equal (item 6). The two
pairing equations of item 1 are not imposed, because they need a positive
invariant Hermitian form, i.e. a unitary `π₂`. The parent task forbids turning the
unitary hypotheses of Proposition 3.1 into hypotheses of this target.

What the omission leaves free is one positive scale, for ranks at least two. Here
is the reason, which is not proved in Lean. The geometric conditions are
homogeneous in the measures. Let `0 < n`, so that the ranks `n + 1` are at least
two, and let `c > 0`. Scale the following by `c`: the quotient measure and its
reflection, `d*a` (by the Weil composition), the second coordinate measure `dx₂`
(Lean `d.dx 1`), `dk`, `d*g`, the coordinate factor `da₂₁ = dx₂`, one factor
`da_1j` with `j ≥ 2`, the intertwining measure and the upper radical measure. Scale
`d*z`, `dz`, `dx₁` and `da₁₁` by `c⁻¹`, and leave the other measures unchanged.
The result is again geometrically normalized. The self-duality of
`dx₁ ⋯ dx_{n+1}` survives because `dx₁` and `dx₂` change by inverse factors. The
compact volumes of items 2 and 3, the Iwasawa equation of item 4 and the equations
of items 5–7 are each preserved. Conversely, the conditions force the intertwining
measure to scale exactly like `d*a·dn₂`. The Jacquet measures enter (0.3) on both
sides with the same scale, so `C` scales by `c⁻¹`. The page-76 observation is that
item 1 fixes exactly `d*a·dn₂`. Hence, for ranks at least two, the equal-rank
statement holds exactly when `C / (ω(−1)^{m+1} G)` is a positive real constant for
some, equivalently any, geometric normalization. That is the content of the
source's "there exists a normalization of measures", now with the coupling of
pages 75–77 imposed on the measures themselves.

**Rank one.** For `G₁ × G₁` (Lean `n = 0`) the recipe degenerates, and the
equal-rank part excludes this case. Here `G_{n−1} = G₀` and `U₁` are trivial and
there is a single coordinate `dx₁ = dz`. Because `ψ` has conductor `O`, the
self-dual measure gives `O^×` the volume `1 − q^{−1}`. So item 3 fixes `dz`, and
`d*z` with it, and item 2 then fixes the total mass of `d*a·dn₂` on the trivial
groups. If those trivial groups carry unit masses, as the source's formulas
suggest, item 2 gives `∫_{O^×} d*z = 1`, and this contradicts the self-duality of
item 3. If the masses are free, as in the published data structure, the
conditions pin the intertwining measure: it is the self-dual measure. The shared
Jacquet measure stays free, but its scale cancels in (0.3), so `C` is pinned as
well. Imposing that on Theorem 5.1 would turn the source's
existential into an assertion with a specific constant that the source does not
make. So rank one is covered only by the all-rank part.

**All ranks: item 6 extended.** For `m ≠ n` the source gives no general recipe
(see above), so the all-rank statement keeps the theorem's existential
quantifier. It imposes the one condition that makes sense for every pair of
ranks: the two Jacquet functionals use the product measure of the same scalar
Haar measure `ν_J`. This extends item 6 and Section 4's `db = db'`. It is a
derived normalization, not a source recipe. Section 4's remaining conditions for
`(n − 1, n)` (`dX' = dY` and its items 2–7) are not formalized; that is a retained
gap. Two remarks show that this form loses nothing. Neither is proved here.

- Every Haar measure on `M_{a×b}(F)` is a positive multiple `c` of a product
  measure, and scaling `ν` by `c^{1/(ab)}` scales `rectangularMeasure ν a b` by
  `c`. So asking for product measures is no restriction.
- Scaling `μ` by `a > 0`, `μJ` by `b > 0` and `μJ'` by `c > 0` replaces `C` by
  `(b / (a c)) C`. Hence the all-rank statement also holds exactly when
  `C / (ω(−1)^{m+1} G)` is a positive real constant for some, equivalently any,
  admissible choice of measures. Tying the Jacquet measures together through
  `ν_J` removes the freedom, pointed out in the review of `f4aaa918`, to scale
  `μ` and `μJ` together without changing `C`.

Page 68 also says that "these normalized measures are in fact independent of the
representations `π₁` and `π₂`". That stronger form, with the measures chosen before
`π₁` and `π₂`, is a remark rather than part of Theorem 5.1. It is not formalized
here.

## Conventions

- **The gamma factor.** The parent task fixes `ε'` as the page-68 factor
  `ε L(1 − s, π̃₁ × π̃₂) / L(s, π₁ × π₂)`. The Library's gamma relations are
  Henniart's definition (2.3.4) of this quotient through the JPSS functional
  equations (published `GammaFactor` module). The raw epsilon factor is not
  used.
- **Rank order.** Shahidi's notation puts the smaller rank first. Page 102 takes
  `π₁` on `G_m` and `π₂` on `G_n`. For `m ≤ n − 1`, page 103 defines
  `ε'(s, π₁ × π₂, ψ)` by (5.1), whose integral `Ψ` pairs the larger-rank `W₂`
  with the smaller-rank `W₁`. For `m > n`, page 103 sets `ε'(s, π₁ × π₂, ψ) =
  ε'(s, π₂ × π₁, ψ)`, and for `m = n` page 102 notes the same symmetry. So `ε'`
  is symmetric by definition. The published `IsPadicPairGammaFactor` instead
  puts the larger rank first (JPSS (2.12)), and `IsPadicSymmetricGammaFactor`
  extends it to both orders by swapping. For the pair `(π₁, π̃₂)` it is the pair
  relation for `(π₁, π̃₂)` when `n ≤ m`, and the one for `(π̃₂, π₁)` when
  `m < n`. The translation only changes the order in which the pair is
  written: in both conventions the larger-rank representation is the one in
  its `ψ`-model (next item).
- **ψ against ψ̄.** In the Library's pair relation the larger-rank candidate is
  in its `ψ`-Whittaker model and the test representation is in its `ψ̄`-model
  (`glInverseFunctionals`). In Shahidi's integral `Ψ` on page 103, the
  larger-rank `W₂` is in the `ψ`-model, and the smaller-rank factor is
  `W₁(ε_m g)`. By the published `Signs` module, left translation by the
  alternating diagonal `ε_m` turns a `ψ`-Whittaker function into a `ψ̄`-Whittaker
  function. So both integrals pair the `ψ`-model of the larger rank with a
  `ψ̄`-model of the smaller rank. The local coefficient uses the `ψ`-functionals of
  both `π₁` and `π₂`, as in (0.2).
- **Absolute value and induction.** The induced space `I(s, π₁ ⊗ π₂)` is the
  published p-adic one of `Induction`, with the normalized absolute value. That
  module documents the source's induction-exponent display, its translation to the
  Library's normalized induction, and its use of smooth rather than `K_r`-finite
  functions.

## What is not claimed

The module does not prove Theorem 5.1, the existence of the local coefficient,
the existence of the gamma factor, or the existence of a geometrically normalized
datum. It does not state Proposition 3.1, Proposition 4.2, Lemma 5.1, the
multiplicativity of `C_χ` or `ε'`, or the Plancherel formulas of Section 6. It does
not state the Section 4 normalization for `(n − 1, n)`, the pages 75–77 normalization
at rank one, or the page-68 independence
of the normalized measures from `π₁` and `π₂`. It is stated for p-adic fields
(finite extensions of `ℚ_p`), the setting of the published gamma relations
`IsPadicPairGammaFactor` and `IsPadicSymmetricGammaFactor`.

## Lean checks

`lean_check` of `Langlands.Representation.Shahidi.LocalCoefficientGammaStatement`
compiles with 0 errors and 0 warnings. The inspected declaration
`Langlands.Shahidi.LocalCoefficientGammaStatement` is a definition with level
parameters `uF` and `uV`. Its type is `Prop`, and it depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. The theorems
`blockWeyl_mul_self_equalRanks`, `blockWeyl_inv_mul_upper_equalRanks`,
`isEqualRankMeasureNormalized_iff`, `IsEqualRankMeasureNormalized.geometric` and
`IsEqualRankGeometricNormalized.radical_coordinates` are proved. The auxiliary
theorem `localCoefficientGammaTopologicalRing` records that the canonical topology
of a p-adic field is a ring topology; the statement uses it to supply the
topological-ring instance required by the coordinate conditions.
