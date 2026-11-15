# The idele slab measure of the equal-rank Rankin–Selberg integral

This module proves the facts about the idele measure `d^×a = ideleMeasure F` that make the
unfolding of the equal-rank global integral exact. They are the facts that the Markdown of
`Langlands.Global.RankinSelberg.EqualIntegrals` uses to explain its normalization and does
not prove: the slab volume `ideleSlabVolume F` is finite and nonzero, and the slab cuts
every fiber `F^× \ 𝔸^×` in a set of measure one. Every result holds for every number field
`F` in an arbitrary universe `u`. Neither compactness of `F \ 𝔸` nor any automorphic datum is
assumed.

Notation: `Points F n` is `GL_n(𝔸)`, `Γ₁ = AdelicGroupPoints.rationalSubgroup F (Scheme F 1)`
is `F^× = GL_1(F)` inside `GL_1(𝔸) = 𝔸^×`, `|z| = detNorm F 1 z` is the idelic absolute
value of the determinant, and `e = Real.exp 1`. The two local instances
`ideleSchemeAffine` and `ideleSchemeSmooth` restate, for `Scheme F n`, the published
`GroupScheme.GeneralLinear.isAffine_groupScheme` and `GroupScheme.GeneralLinear.smoothStatement`,
exactly as the local instances of `EqualIntegrals` do, so that the quotient Haar measure is
available.

## The packaged statement

`IdeleFiberMassStatement.{u}` is the proposition: for every number field `K : Type u`,

1. `ideleSlabVolume K ≠ 0` and `ideleSlabVolume K ≠ ⊤`;
2. for every real `c > 0`, the slab `determinantSlab K 1 c (e * c)`, that is,
   `K^× \ {c ≤ |a| < e c}`, has volume `ideleSlabVolume K` for
   `AdelicGroupPoints.rationalQuotientHaarMeasure K (Scheme K 1)`;
3. for every set `D ⊆ GL_1(𝔸_K)` that is a fundamental domain of `Γ₁` for Mathlib's Haar
   measure (`MeasureTheory.IsFundamentalDomain`), and every real `c > 0`,
   `ideleMeasure K (D ∩ {z | c ≤ |z| ∧ |z| < e * c}) = 1` and
   `ideleMeasure K (D ∩ {z | c < |z| ∧ |z| ≤ e * c}) = 1`.

The theorem `ideleFiberMass` proves it, by assembling the separate results below.

## Results

* `points_one_mul_comm`: `GL_1(𝔸)` is commutative. A `1 × 1` invertible adelic matrix is
  the scalar matrix of its determinant (`AdelicGL.scalar_determinant_one`), and scalar
  matrices commute with everything (`AdelicGL.scalar_commute`); the published group
  isomorphism `GeneralLinearGroupPoints.adelicEquiv F 1` transfers this to `Points F 1`.
* `isMulRightInvariant_haar_points_one` and `isInvInvariant_haar_points_one` (instances):
  Mathlib's Haar measure on `GL_1(𝔸)` is right invariant and inversion invariant. Right
  multiplication equals left multiplication by commutativity. Inversion invariance is
  Mathlib's `IsHaarMeasure.isInvInvariant_of_regular` for the commutative group structure
  with the same multiplication.
* `detNorm_inv`: `|det x⁻¹| = |det x|⁻¹` in `GL_n(𝔸)`, from multiplicativity
  (`Unfolding.detNorm_mul`).
* `detNorm_rationalSubgroup_mul`: `|det (k x)| = |det x|` for `k ∈ GL_n(F)`, from
  multiplicativity and the product formula (`Unfolding.detNorm_of_mem_rationalSubgroup`).
* `exists_detNorm_eq`: every real `c > 0` is `|z|` for some `z ∈ GL_1(𝔸)`, namely the
  scalar matrix of the idele `IdeleAbsoluteValue.normSection F c`, whose normalized absolute
  value is `c` (`IdeleAbsoluteValue.full_normSection`).
* `mk_mem_determinantSlab_iff`, `preimage_mk_determinantSlab`: the class of `g` lies in
  `determinantSlab F n a b` if and only if `a ≤ |det g| < b`; so the preimage of the slab in
  `GL_n(𝔸)` is exactly `{g | a ≤ |det g| < b}`. This uses `detNorm_rationalSubgroup_mul`.
* `measurableSet_detNorm_Ico`, `measurableSet_determinantSlab`: these sets are measurable,
  by continuity of `detNorm` (`Unfolding.continuous_detNorm`) and the definition of the
  quotient σ-algebra.
* `rationalQuotientHaarMeasure_determinantSlab_eq`: for every fundamental domain `D` of
  `GL_n(F)` in `GL_n(𝔸)` for Haar measure, the quotient measure of the slab is
  `haar (D ∩ {g | a ≤ |det g| < b})`. This is `AdelicGroupPoints.rationalQuotientHaarMeasure_eq`
  (the quotient Haar measure computed from any fundamental domain) with
  `LeftCosetSpace.quotientMeasure_apply` and the preimage formula.
* `rationalQuotientHaarMeasure_determinantSlab_mul`: for `t ∈ GL_1(𝔸)`, the slabs
  `[a |t|, b |t|)` and `[a, b)` of `GL_1(F) \ GL_1(𝔸)` have the same volume. Right
  translation by `t` preserves the quotient Haar measure
  (`AdelicGroupPoints.measurePreserving_rightTranslate_rationalQuotientHaarMeasure`, which
  needs the right invariance above), and it pulls the first slab back to the second, since
  `|g t| = |g| |t|` and `|t| > 0`.
* `rationalQuotientHaarMeasure_determinantSlab`: for `c > 0`, the slab `[c, e c)` has volume
  `ideleSlabVolume F`. Take `t` with `|t| = c` and apply the previous result with `a = 1`,
  `b = e`.
* `ideleSlabVolume_ne_top`: the slab volume is finite.
  `AdelicGL.exists_isCompact_determinantBandCover F 1 e` (published in
  `Langlands.Automorphic.RankOneDeterminantBand`) gives a compact set `K` of invertible
  `1 × 1` adelic matrices such that every matrix with determinant norm in `[1, e]` has a
  rational left multiple in `K`. Its preimage `K'` under the published homeomorphism
  `GeneralLinearGroupPoints.adelicHomeomorph F 1` is compact, the slab `[1, e)` lies in the
  image of `K'` in the quotient (the rational multiple lies in the same class), and this image
  is compact, hence of finite measure for the locally finite quotient Haar measure.
* `ideleSlabVolume_ne_zero`: the slab volume is nonzero. Take the fundamental domain `D` of
  `Γ₁` given by `LeftCosetSpace.isFundamentalDomain` (`Γ₁` is discrete by
  `AdelicGroupPoints.isDiscrete_rationalSubgroup`). If the slab volume were zero, then
  `haar (D ∩ S) = 0` for the `Γ₁`-invariant set `S = {1 ≤ |g| < e}`, so `haar S = 0` by
  Mathlib's `IsFundamentalDomain.measure_zero_of_invariant`. But `S` contains the open set
  `{1 < |g| < e}`, which is nonempty (it contains a point of norm `exp (1/2)`), and Haar
  measure is positive on nonempty open sets.
* `ideleMeasure_fundamentalDomain_Ico`: for every fundamental domain `D` of `Γ₁` and
  `c > 0`, `ideleMeasure F (D ∩ {c ≤ |z| < e c}) = 1`. By definition
  `ideleMeasure F = (ideleSlabVolume F)⁻¹ • haar`; the Haar measure of the set is the slab
  volume of `[c, e c)`, which is `ideleSlabVolume F`; and `v⁻¹ v = 1` because `v` is
  neither `0` nor `⊤`.
* `isFundamentalDomain_preimage_inv`: if `D` is a fundamental domain of `Γ₁`, so is
  `{z | z⁻¹ ∈ D}`. This is Mathlib's `IsFundamentalDomain.preimage_of_equiv` for the
  measure-preserving inversion, with `k ↦ k⁻¹` on `Γ₁`; it uses `(k⁻¹ x)⁻¹ = k x⁻¹`, which
  holds by commutativity.
* `ideleMeasure_fundamentalDomain_Ioc`: for every fundamental domain `D` of `Γ₁` and
  `c > 0`, `ideleMeasure F (D ∩ {c < |z| ≤ e c}) = 1`. Inversion preserves Haar measure and
  maps `D ∩ {c < |z| ≤ e c}` onto `{z⁻¹ ∈ D} ∩ {1/(e c) ≤ |z| < 1/c}`, and
  `1/c = e · 1/(e c)`; apply the `Ico` result to the inverted fundamental domain with
  `1/(e c)` in place of `c`.

## Use in the unfolding

In Cogdell's unfolding of the equal-rank integral (2004, §2.3, printed p.210, PDF p.213),
replacing the Eisenstein series by its definition and unfolding turns the integral over
`Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` against the section
`|det g|^s ∫_(𝔸^×) Φ(a e_n g) |a|^(ns) η(a) d^×a` (printed p.208, PDF p.211) into an
integral over
`P_n(F) \ GL_n(𝔸)`. The idele integral and the central quotient recombine there. With the
Library's measures (`centralQuotientMeasure`, the quotient measure restricted to the slab
`1 ≤ |det g| < e^n`), the idele variable `a` then ranges, for fixed `g`, over
`D ∩ {c ≤ |a| < e c}` with `c = |det g|^(-1/n)`, for a fundamental domain `D` of `F^×`
in `𝔸^×`. The result `ideleMeasure_fundamentalDomain_Ico` (or its `Ioc` form, after the
substitution `a ↦ a⁻¹`) shows that this set has measure one, so the unfolded identity holds
with constant `1`. This paragraph explains the intended use; this module does not state or
prove the unfolding.

## Provenance

Internal. The statements are standard measure-theoretic facts about `𝔸^×` that the
normalization of `ideleMeasure` in `EqualIntegrals` relies on; Cogdell (2004, §2.3, p.208)
writes `d^×a` without fixing its normalization and uses these facts implicitly in the
unfolding on p.210. The proofs here are internal, built from the published compact
determinant-band cover, the norm section of the idelic absolute value, the published quotient
Haar measure and its right-translation invariance, and Mathlib's fundamental-domain and Haar
measure theory.
