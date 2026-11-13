# Renard II.3.13: centrality, Hecke commutation and conjugation invariance

Worker 108, Task 5531. Source: Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, II.3.13 Corollary and
the first paragraph of its proof, printed p.55 / PDF p.61; source
registration `renard-2026-representations-groupes-reductifs-padiques`.

This helper module proves that `CentralitySpecification μ pr` holds for
every right product `pr` satisfying the published
`RenardEssentialProducts.RightProductSpecification μ pr`
(theorem `centrality`). The final proof of `RenardCenter.Statements` uses it.
It imports the criteria proof `RenardCenterCriteriaProof` for its sampling
and indicator lemmas.

## Evaluation formulas

`rightHeckeConvolution_eq`: `(T * h)(f) = T(F)` for the test `F` with
`F x = ∫ h(z) f(xz) dμ(z)`. The published action evaluates `T` on the test
convolution of `f` with the inverted `h`. The substitution `y = xz` uses left
invariance of `μ` (`integral_mul_left_eq_self`).
`leftHeckeConvolution_eq`: `(h * T)(f) = T(F)` with
`F x = ∫ h(y) f(yx) dμ(y)`. The published left action integrates against
`μ.inv = map inv μ`, and `integral_map` undoes the inversion.

## Hecke commutation is conjugation invariance

This holds for every algebraic distribution `T`
(`commute_iff_isConjugationInvariant`). Both directions pass through the
translation condition, which the criteria proof shows to be equivalent to
conjugation invariance.

* `commute_of_translation`: given `f` and `h`, `exists_sampling_level_two_sided`
  gives an open subgroup `K`. With it, `h` is right `K`-invariant and `f` is
  right `K`-invariant. Also `f` is left invariant under `y K y⁻¹` for `y` in
  the support of `h`. It uses the published common bi-invariance and
  `exists_openSubgroup_conj_mem`. Sampling (`integral_eq_sampleWeight`) then
  writes the test for `T * h` as `Σᵢ dᵢ · rightTranslate pᵢ f`. It writes the
  test for `h * T` as `Σᵢ dᵢ · leftTranslate pᵢ⁻¹ f`, with the same weights.
  The translation identity at `pᵢ⁻¹` equates the two `T`-values term by term.
* `translation_of_commute`: given `g` and `f`, take `K₀` fixing `f` on both
  sides and a compact open `K ≤ K₀ ∩ g K₀ g⁻¹`. Let `h` be the normalized
  indicator of `g⁻¹K`. Integration against `h` evaluates at `g⁻¹` any
  function constant on `g⁻¹K` (`integral_leftTranslate_indicator`). So
  `T * h` and `h * T` evaluate `T` on `rightTranslate g⁻¹ f` and
  `leftTranslate g f`. Their equality is the translation identity.

## The centrality specification

`eq_of_rightHeckeConvolution_eq`: if `D * h = D' * h` for all Hecke `h`, then
`D = D'`. For a test `f`, take `K` fixing `f` on the right and let `e` be the
normalized indicator of `K`. Then `(D * e)(f) = D(f)`.

`centrality` uses three parts of the right-product specification:
associativity of `pr`, the Hecke-lift clause of `AlgebraLaws`, and its third
clause. The Hecke-lift clause supplies, for each Hecke `h`, the element `H`
of `rightEssentiallyCompact μ` with underlying distribution `h μ`. It
satisfies `pr S H = S * h` and `pr H S = h * S` for all `S`. The third
clause says `U * h` is a Hecke distribution `k μ`.

1. If `T` commutes with every `U` under `pr`, then taking `U = H` gives
   `T * h = h * T`.
2. Conversely, assume `T * h = h * T` for all `h`, and let `U` be arbitrary.
   Then `pr (pr T U) H = pr T (pr U H)`. Since `pr U H` is the lift of `k`,
   this is `T * k = k * T = pr (pr U H) T`. By associativity this equals
   `pr U (pr H T) = pr U (pr T H) = pr (pr U T) H`. Hence `pr T U` and
   `pr U T` have the same right Hecke products, and they are equal.
3. The middle equivalence is `commute_iff_isConjugationInvariant`.
4. If `T` is conjugation invariant, then `h * T = T * h` is compactly
   supported for every `h`, because `T` is right essentially compact. So `T`
   is also left essentially compact, hence in `essentiallyCompact μ`.

This follows the source: the center of the right essentially compact
algebra is the commutant of `H(G)`, such distributions are two-sided
essentially compact, and commutation is conjugation invariance by the
criteria of II.3.13.
