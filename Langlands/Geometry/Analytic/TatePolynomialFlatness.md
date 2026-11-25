# Flatness of polynomial algebras in strict Tate algebras

This helper module proves that the polynomial map
`polynomialMap n : K[T₁, …, Tₙ] → K⟨T₁, …, Tₙ⟩` (`MvPolynomial.aeval` of the
Tate coordinates `StrictTateAlgebra.X`) is flat (`flat_polynomialMap`). Here
`K : Type u` is a complete, ultrametric, nontrivially normed field and
`K⟨T₁, …, Tₙ⟩ = StrictTateAlgebra (Fin n) K`. The module serves the
chart-flatness proof in `AffineAnalytificationChartFlatProof`. Everything lives
in the namespace `Langlands.Analytic.TatePolynomialFlatness`.

## Provenance

This is internal supporting content for the chart flatness proof. Berkovich
1990, proof of Theorem 3.4.1 (printed pp.63–64, PDF pp.77–78), deduces the
flatness of affinoid algebras over `A` from the isomorphism of completions of
local rings at rigid points (Theorem 3.4.1(ii)), and step (1) of that proof
treats affine space through the algebras `k{r⁻¹T}`. The implemented proof uses
the same idea for `K[T] → K⟨T⟩`: the completions agree at every maximal ideal.
It proves this one variable at a time. Then the Library's one-variable
Weierstrass division can supply the comparison of truncations. The
Nullstellensatz and the induction on the number of variables are standard.
No statement here is attributed to the literature beyond this.

## Declarations

- `quotientMap_bijective_of_forall`: a membership criterion for bijectivity of
  `Ideal.quotientMap I f h : R ⧸ J → S ⧸ I`. It is injective if `f r ∈ I`
  implies `r ∈ J`. It is surjective if every `s` is congruent to some `f r`
  modulo `I`. `quotientMap_bijective_congr` transports bijectivity along an
  equality of target ideals.
- `not_isField_succ m`: `K⟨T₀, …, Tₘ⟩` is not a field. `T₀` is nonzero (its
  norm is `1`), and every product `T₀ v` has constant coefficient `0`, so `T₀`
  has no inverse.
- `finite_quotient_of_isMaximal`: for a maximal ideal `𝔪` of `K⟨T₁, …, T_N⟩`,
  the residue field is a finite-dimensional `K`-vector space (Nullstellensatz).
  *Proof.* `𝔪` is closed (`isClosed_ideal_of_noetherian_banach`; the Tate
  algebra is Noetherian by `TateNoetherian`), so the quotient is a presented
  strict affinoid algebra. The Library's
  `PresentedStrictAffinoidAlgebra.exists_noetherNormalization` gives an
  injective finite map `K⟨T₁, …, Tₘ⟩ → K⟨T⟩ ⧸ 𝔪`. The target is a field and
  integral over the source, so the source is a field
  (`isField_of_isIntegral_of_isField`). By `not_isField_succ`, `m = 0`. Then
  `K → K⟨⟩` is surjective (`zeroVariables_algebraMap_surjective`), and the
  composite `K → K⟨T⟩ ⧸ 𝔪` is finite.
- `exists_last_max_coeff`: a nonzero `p : K[X]` has an index `d` with
  `p.coeff d ≠ 0`. Every coefficient has norm at most `‖p.coeff d‖`, and
  every coefficient beyond `d` has strictly smaller norm.
- `isDistinguished_ofPolynomial_map`: for such `d`, the image of `p` in
  `A⟨X⟩` is distinguished at index `d` (`RestrictedSeries.IsDistinguished`),
  where `A = K⟨T₁, …, Tₙ⟩` and `A⟨X⟩ = RestrictedSeries.Algebra A`. Constants
  of `K` keep their norm in `A`, and a nonzero constant is a unit.
- `exists_monic_mem n 𝔪`: every maximal ideal `𝔪` of `A⟨X⟩` contains
  `ofPolynomial w` for some monic `w ∈ A[X]` whose coefficients all have norm
  at most `1`.
  *Proof.* Pull `𝔪` back along `StrictTateAlgebra.regroupEquiv n :
  K⟨T₀, …, Tₙ⟩ ≃+* A⟨X⟩`, which sends `T₀` to `X` (`regroup_X_zero`). By the
  Nullstellensatz, `T₀` is integral over `K` modulo the pulled-back ideal. So a
  monic `p ∈ K[X]` has `p(X) ∈ 𝔪`. By `isDistinguished_ofPolynomial_map`, the
  image of `p` is distinguished. The Library's
  `RestrictedSeries.existsUnique_distinguished_preparation` writes it as a unit
  times `ofPolynomial w`, where `w` is monic with coefficients of norm at most
  `1`. Hence `ofPolynomial w ∈ 𝔪`.
- `pow_coeff_le`: powers of such a `w` again have coefficients of norm at most
  `1`, by submultiplicativity of the norm on `A⟨X⟩`.
- `exists_sub_mem_span`: for such a monic `w`, every `g ∈ A⟨X⟩` is congruent
  to some polynomial modulo `ofPolynomial w`
  (`RestrictedSeries.weierstrassQuotientMap_surjective`).
- `flat_ofPolynomial n`: `RestrictedSeries.ofPolynomial A : A[X] → A⟨X⟩` is
  flat.
- `polynomialMap_zero_bijective`: with no variables, `polynomialMap 0` is
  bijective.
- `regroup_comp_polynomialMap n`: after `regroupEquiv n`, `polynomialMap (n+1)`
  equals `MvPolynomial.finSuccEquiv`, then `Polynomial.map (polynomialMap n)`,
  then `ofPolynomial`. Both sides are checked on constants and variables.
- `flat_mapRingHom`: if `φ : R → S` is flat, then so is
  `Polynomial.mapRingHom φ : R[X] → S[X]`. This is Mathlib's stability of
  flatness under base change, applied to the pushout square of polynomial
  rings.
- `flat_polynomialMap n`: the main result.

## Proof of `flat_ofPolynomial`

`A⟨X⟩` is Noetherian, being isomorphic to `K⟨T₀, …, Tₙ⟩`, and `A[X]` is
Noetherian. By `TruncatedComparison.flat_of_forall_maximal`, it suffices to
show that `A⟨X⟩_𝔪` is flat over `A[X]` for every maximal ideal `𝔪` of `A⟨X⟩`.
Let `𝔫 = 𝔪 ∩ A[X]`, and choose `w` as in `exists_monic_mem`, so `w ∈ 𝔫`.

1. `𝔫 A⟨X⟩ = 𝔪`. Take `b ∈ 𝔪` and write `b = (b - r) + r` with `r` a
   polynomial and `b - r ∈ (w)` (`exists_sub_mem_span`). Then `r ∈ 𝔪`, so
   `r ∈ 𝔫`, and `(w) ⊆ 𝔫 A⟨X⟩`.
2. For every `k`, `A[X] ⧸ (w ^ k) → A⟨X⟩ ⧸ (w ^ k)` is bijective. Injectivity
   is `RestrictedSeries.ofPolynomial_mem_span_iff` for the monic `w ^ k`, and
   surjectivity is `exists_sub_mem_span` for `w ^ k`. Both use
   `pow_coeff_le`.
3. Since `(w ^ k) ≤ 𝔫 ^ k`, `TruncatedComparison.quotientMap_bijective_of_le`
   makes `A[X] ⧸ 𝔫 ^ k → A⟨X⟩ ⧸ 𝔫 ^ k A⟨X⟩` bijective. By step 1, the target
   ideal is `𝔪 ^ k`.
4. `TruncatedComparison.flat_localization` with `𝔫 ≤ 𝔪 ∩ A[X]` concludes.

## Proof of `flat_polynomialMap`

Induction on `n`. For `n = 0` the map is bijective, so it is flat
(`RingHom.Flat.of_bijective`). For `n + 1`, the right-hand side of
`regroup_comp_polynomialMap` is a composite of flat maps: the bijection
`finSuccEquiv`, then `Polynomial.mapRingHom (polynomialMap n)` (flat by the
induction hypothesis and `flat_mapRingHom`), then `flat_ofPolynomial n`. The
bijective `regroupEquiv n` on the left can be removed
(`RingHom.Flat.comp_iff_of_bijective_left`).

## Scope

The results concern the strict Tate algebras `K⟨T₁, …, Tₙ⟩` of radius `1`. The
module `AffineAnalytificationChartFlatProof` transfers them to the
polyradius of the charts by rescaling.
