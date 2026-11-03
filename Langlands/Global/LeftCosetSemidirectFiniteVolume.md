# Finite covolume for topological semidirect products

This module proves that finite Haar covolume of discrete subgroups is inherited by a
topological semidirect product from its factors. It works with the
`haarQuotientMeasure` of `LeftCosetHaarMeasure`, the quotient of the actual Mathlib
`Measure.haar` by a discrete subgroup, and with the chosen Borel fundamental domain
`fundamentalDomain` of `LeftCosetFundamentalDomain`. All groups in the measure
statements are topological groups that are locally compact and second countable, with
their Borel sigma algebras. No Hausdorff or unimodularity hypothesis is assumed;
unimodularity of the quotient factor is proved.

## Unimodularity

`isMulRightInvariant_haar_of_isFiniteMeasure`: if a discrete subgroup `Γ ≤ M` has
finite Haar covolume, then `Measure.haar` on `M` is right invariant. A right
translate `E g` of the fundamental domain `E` is again a fundamental domain
(`IsFundamentalDomain.preimage_of_equiv`), so the left-invariant measure
`map (· * g) haar` gives `E` the same mass as `haar` does. By uniqueness of Haar measure
it is `c • haar`, and `0 < haar E < ∞` (the total mass of the nonzero finite quotient
measure) forces `c = 1`.

## Automorphisms and characters (one group `G`)

* `haar_fundamentalDomain_ne_zero` and `haar_fundamentalDomain_ne_top`: the chosen
  fundamental domain of a discrete subgroup `Λ` has nonzero Haar measure, and finite
  Haar measure when the quotient measure is finite. Both read off the total mass of the
  quotient measure.
* `isFiniteMeasure_haarQuotientMeasure_of_isCompact`: if one compact set `K` meets
  every orbit, i.e. `∀ g, ∃ γ ∈ Λ, γ * g ∈ K`, then the quotient has finite measure. The
  quotient image of a measurable hull of `K` is everything, and
  `quotientMeasure_image_le` bounds its mass by `haar K < ∞`.
* `mulEquivHaarChar_eq_one_of_forall_mem_iff`: a topological group automorphism `φ`
  with `φ g ∈ Λ ↔ g ∈ Λ` has Mathlib modulus `mulEquivHaarChar φ = 1` when `Λ` has
  finite covolume. The preimage `φ⁻¹ E` is a fundamental domain, so it has the mass of
  `E`, while `mulEquivHaarChar_smul_preimage` multiplies that mass by the modulus.
* `eq_one_of_measurable_of_isFiniteMeasure`: a measurable multiplicative function
  `δ : G → ℝ≥0` with nonzero values that is `1` on `Λ` is identically `1`, when `Λ` has
  finite covolume. Otherwise some `g1` has `s = δ g1 > 1`. Haar measure is right
  invariant by the unimodularity theorem, so for every threshold `t` the
  `Λ`-invariant set `{δ < t}` and its right translate `{δ · s < t}` meet `E` in sets of
  equal finite measure (`IsFundamentalDomain.measure_set_eq` for the translated domain).
  Hence each band `{δ < t} \ {δ · s < t}` meets `E` in a null set. The bands with
  `t = s ^ (k + 1)`, `k : ℤ`, cover `G` (`NNReal.exists_mem_Ico_zpow`), so `haar E = 0`,
  contradicting the first item.

## Semidirect products

Algebraic data: group homomorphisms `i : N →* H`, `j : M →* H`, `p : H →* M` with
`p (j m) = m` (`hpj`), `p (i n) = 1` (`hpi`), and every `h` with `p h = 1` in the
range of `i` (`hker`).

* `normalPart h` is a chosen `n` with `i n = h * (j (p h))⁻¹`
  (`i_normalPart`, `i_normalPart_mul_j_p`). For injective `i`,
  `normalPart (i n * j m) = n`.
* `conjFun m n` is `normalPart (j m * i n * (j m)⁻¹)`, so
  `i (conjFun m n) = j m * i n * (j m)⁻¹` (`i_conjFun`).

Topological data: `i` is a topological embedding, `j` and `p` are continuous, and `H`
is a topological group.

* `prodHomeomorph : N × M ≃ₜ H` is `(n, m) ↦ i n * j m`, with inverse
  `h ↦ (normalPart h, p h)`; continuity of `normalPart` follows from the embedding
  property of `i`.
* `conj m : N ≃ₜ* N` is conjugation by `j m`, with inverse `conj m⁻¹`;
  `i_conj` gives its image under `i`, `conj_mul` gives
  `conj (m * m') = (conj m').trans (conj m)`, and `i_mul_j_mul_i_mul_j` is the
  multiplication law
  `i n' * j m' * (i n * j m) = i (n' * conj m' n) * j (m' * m)`.

Measure statements, with all three groups locally compact, second countable and
Borel:

* `mulEquivHaarChar_conj_mul`: `m ↦ mulEquivHaarChar (conj m)` is multiplicative
  (Mathlib `mulEquivHaarChar_trans`).
* `measurable_mulEquivHaarChar_conj`: this modulus is measurable. For a compact
  neighbourhood `K0` of `1` with interior `U`, the modulus of `conj m` equals
  `haar U / haar ((conj m)⁻¹ U)`. The denominator is the measure of the slice at `m` of
  the open set `{(m, n) | conj m n ∈ U}` of `M × N`, measurable in `m` by
  `measurable_measure_prodMk_left`.
* `mulEquivHaarChar_conj_eq_one_of_mem`: if `j m ∈ Γ`, then `conj m` maps
  `i⁻¹(Γ)` onto itself, and `i⁻¹(Γ)` is discrete (preimage under an injective
  continuous map) and has finite covolume by the compact covering hypothesis. The
  automorphism item gives modulus `1`.
* `exists_haar_eq_smul_map_prod`: if every `conj m` has modulus `1`, then
  `Measure.haar` on `H` is `c • map prodHomeomorph (haar.prod haar)` for some
  `c : ℝ≥0`. Each `conj m` is then measure preserving, so by the multiplication law
  left multiplication by `i n' * j m'` corresponds to the measure-preserving product map
  `(n ↦ n' * conj m' n) × (m ↦ m' * m)`. The transported product measure is therefore
  a left-invariant Haar measure, and uniqueness of Haar measure gives `c`.

## Main theorem

`Semidirect.isFiniteMeasure_haarQuotientMeasure`: in addition let `Γ ≤ H` be
discrete, let `K ⊆ N` be compact with `∀ n, ∃ γ, i γ ∈ Γ ∧ γ * n ∈ K`, and let
`ΓM ≤ M` be discrete with `j γ ∈ Γ` for `γ ∈ ΓM` and
`IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)`. Then
`IsFiniteMeasure (haarQuotientMeasure Γ hΓ)`.

Proof. The conjugation modulus is a measurable multiplicative function with nonzero
values (`mulEquivHaarChar_pos`), equal to `1` on `ΓM`, so it is identically `1` by
`eq_one_of_measurable_of_isFiniteMeasure` applied in `M`. Then
`exists_haar_eq_smul_map_prod` writes Haar measure on `H` as `c` times the transported
product measure. Let `E` be the fundamental domain of `ΓM` and `K'` a measurable hull of
`K`. The set `S = prodHomeomorph (K' ×ˢ E)` has measure `c · haar K · haar E < ∞`. It
meets every `Γ`-orbit: for `h = i n * j m`, choose `γM ∈ ΓM` with `γM * m ∈ E` and then
`γN` with `i γN ∈ Γ` and `γN * conj γM n ∈ K`; the multiplication law places
`(i γN * j γM) * h` in `S`. Hence the quotient image of `S` is everything, and
`quotientMeasure_image_le` bounds the total quotient mass by the measure of `S`.

## Provenance

This is internal support for a planned proof of
`Langlands.Global.AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement`
(finite volume of `G(F) \ G(A)^1`, Getz–Hahn, Theorem 2.6.3). The intended
application is to a Levi decomposition `G = U ⋊ L` with `H = G(A)^1`, `N = U(A)` and
`M = L(A)^1`; this module contains no adelic or algebraic-group content. The
formulation and the proof, including the triviality of the conjugation modulus by the
argument above rather than by computing it, are internal.
