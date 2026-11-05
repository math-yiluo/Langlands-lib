# Fourier inversion on a finite product of circles

Lean module: `Langlands.HarmonicAnalysis.TorusFourierInversion`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports the published
`Langlands.HarmonicAnalysis.TorusFourierDecay` for the characters
`torusCharacter n z = ∏_j z_j^{n_j}` (`torusCharacter_mul`, `norm_torusCharacter`,
`continuous_torusCharacter`), the Fourier coefficients
`torusFourierCoeff μ f n = ∫ f(z) torusCharacter n z dμ(z)`, the angle derivatives
`torusPartialDeriv`, the translation identity `integral_translate_mul_torusCharacter`, the
smoothness lemmas `exists_norm_le_of_isSmooth` and
`isSmoothFiniteTorusFunction_iterate_torusPartialDeriv`, and the decay estimate
`one_add_norm_pow_mul_norm_torusFourierCoeff_le`. Through it, it uses the Library's smoothness
predicate `IsSmoothFiniteTorusFunction` (`RationalOrbitSmoothFunctions`) and its
`IsSmoothFiniteTorusFunction.continuous`. From Mathlib it uses the complex Stone–Weierstrass
theorem `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`,
`Algebra.adjoin_eq_span_of_subset`, `integral_tsum_of_summable_integral_norm`, `continuous_tsum`,
`isOpenPosMeasure_of_mulLeftInvariant_of_compact`, `Continuous.ae_eq_iff_eq`,
`integral_mul_right_eq_self`, `Real.summable_one_div_int_pow` and `Finset.prod_univ_sum`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84): with
  `ϕ(g) = ∫_{A_G} f_ψ(ag) χ_{ω'}(a^{-1}) da`, "On a l'égalité
  `ϕ(g) = ∫_{A_G} χ_{ω'}(a^{-1}) ∫_𝒪 (E^G_G ψ_ω)(g) χ_ω(a) dω da`. La restriction à
  `A_G ∩ K` de `χ_ω` ne dépend pas du point `ω ∈ 𝒪`. Si cette restriction est différente de
  celle de `χ_{ω'}`, on a `ϕ(g) = 0`. Supposons ces restrictions égales. Comme la fonction
  `ω ↦ (E^G_G ψ_ω)(g)` est continue, on peut appliquer la formule d'inversion de Fourier.
  Compte tenu des définitions de nos mesures, on obtient
  `ϕ(g) = ∑_{ω ∈ 𝒪; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`."
- I.1, printed p. 239 (PDF p. 5), the measures: "L'application de restriction
  `Im X(G) → Im X(A_G)` est surjective de noyau fini. On munit `Im X(A_G)` de la mesure de Haar
  de masse totale 1 et `Im X(G)` de la mesure pour laquelle l'application précédente préserve
  localement les mesures." The total mass of the measure on `Im X(G)` is therefore the order
  `d_G` of the kernel of the restriction.

Waldspurger does not state or prove the Fourier inversion formula; he cites it. This module
proves it for a torus written in coordinates, `T = J → Circle` with `J` finite, and an arbitrary
finite left-invariant measure `μ`. The proofs (orthogonality by translation, uniqueness by
Stone–Weierstrass, inversion for absolutely summable coefficients, summability from the decay
estimate, and the averaging over a finite subgroup) are the standard ones; they are derived for
this purpose and do not follow a cited text.

How the last theorem matches the source, as an explanation only (none of it is formalized
here). Take `T = Im X(G)` in coordinates, `μ` the measure of I.1 (mass `d_G`), and
`K = ker(Im X(G) → Im X(A_G))`, of order `d_G`. Then `μ(T) |K|⁻¹ = 1` and
`hasSum_torusFourierCoeff_mul_conj_isTrivialOn` reads
`∑_{n : χ_n|_K = 1} f̂(n) conj(χ_n(z)) = ∑_{w ∈ K} f(z w)`.

The orbit `𝒪` is not `T` itself. III.7, printed p. 273 (PDF p. 39): "Si l'on choisit un point
base `ω ∈ 𝒪`, on a une bijection `Im X(G)/Stab_{X(G)}(ω) → 𝒪`, `χ ↦ ω ⊗ χ`, où
`Stab_{X(G)}(ω) = {χ ∈ X(G); ω ⊗ χ ≃ ω}` (c'est un groupe fini)." Write `S` for the unitary
part of this stabilizer and `q : T → 𝒪`, `χ ↦ ω ⊗ χ`. Twisting by `χ ∈ S` does not change the
central character on `A_G`, so `S ⊆ K`. VI.3, printed p. 302 (PDF p. 68): "On munit `𝒪` d'une
mesure telle que l'application `Im X(M) → 𝒪`, `χ ↦ ω ⊗ χ` préserve localement les mesures."
Hence `∫_𝒪 F(ω) dω = |S|⁻¹ ∫_T F(q(χ)) dμ(χ)` (in the Library,
`rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral` in `RationalOrbitIntegration`). For a
pulled-back function `f = F ∘ q`, the map `q` sends the coset `zK` onto the orbit fibre
`{ω' ∈ 𝒪 ; χ_{ω'} = χ_{q(z)}}` and is `|S|`-to-one there, so
`∑_{w ∈ K} f(z w) = |S| ∑_{ω' ∈ q(zK)} F(ω')`. This factor `|S|` cancels the factor `|S|⁻¹`
of the orbit integral in `ϕ(g)`, which leaves Waldspurger's
`∑_{ω ∈ 𝒪; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`. With a trivial stabilizer the two sums agree
directly. On the other side, the integral over `A_G` becomes a sum over `A_G` modulo `A_G ∩ K`
(here `K` is Waldspurger's compact open subgroup of I.1, not the finite subgroup of this module)
once the characters trivial on the finite kernel are identified with the image of `A_G` in the
lattice dual to `T`.

## Scope and hypotheses

`J` is a finite type (`Fintype J`). The torus is `J → Circle` with its product group structure
and the product of the Borel measurable spaces. The norm on `J → ℤ` is the sup norm. Waldspurger's
`Im X(G)`, `A_G`, the orbit `𝒪`, the functions `E^G_G ψ_ω` and the identifications described above
are not formalized here.

Hypotheses of the results:

- `torusCharacter_zero`, `torusCharacter_add`, `torusCharacter_neg`, `torusCharacter_inv`,
  `torusCharacterMap_apply`, `torusCharacterSubalgebra_coe`,
  `torusCharacterSubalgebra_separatesPoints`, `span_torusCharacterMap_closure_eq_top`,
  `summable_one_add_abs_sq_inv`, `summable_prod_one_add_abs_sq_inv`, `torusCharacter_mul_mem`:
  none.
- `torusCharacter_single`: `DecidableEq J`.
- `integrable_mul_torusCharacter`: `μ` finite (`IsFiniteMeasure μ`), `hf : Continuous f`.
- `integral_torusCharacter`: `μ` left-invariant (`μ.IsMulLeftInvariant`). No finiteness is
  assumed; `μ.real univ` is the real mass of `μ`, which is `0` when `μ(T) = ∞`.
- `torusFourierCoeff_tsum`: `μ` finite and left-invariant, `hc : Summable fun m => ‖c m‖`.
- `eq_zero_of_torusFourierCoeff_eq_zero`: `μ` finite and positive on nonempty open sets
  (`μ.IsOpenPosMeasure`), `hh : Continuous h`, and `h0 : ∀ n, torusFourierCoeff μ h n = 0`.
- `hasSum_torusFourierCoeff_mul_conj`: `μ` finite and left-invariant, `hf : Continuous f`,
  `hs : Summable fun n => ‖torusFourierCoeff μ f n‖`. The zero measure is allowed (both sides
  are `0`); otherwise positivity on open sets is derived from invariance.
- `hasSum_torusFourierCoeff_mul_conj_of_isProbabilityMeasure`: `μ` a left-invariant probability
  measure, `hf`, `hs`.
- `summable_norm_torusFourierCoeff`, `hasSum_torusFourierCoeff_mul_conj_of_isSmooth`:
  `DecidableEq J`, `μ` finite and left-invariant, `hf : IsSmoothFiniteTorusFunction f`.
- `sum_torusCharacter_subgroup`: `K` a subgroup of `J → Circle` with `Fintype K`, and decidability
  of `IsTrivialOn K n`.
- `integral_mul_right_mul_torusCharacter`: `μ` left-invariant. No finiteness is assumed.
- `hasSum_torusFourierCoeff_mul_conj_isTrivialOn`: `μ` finite and left-invariant, `K` a subgroup
  with `Fintype K`, `DecidablePred (IsTrivialOn K)`, `hf : Continuous f`, and `hs` as above.

## Definitions

- `torusCharacterMap n : C(J → Circle, ℂ)`, the character `χ_n = torusCharacter n` as a
  continuous function.
- `torusCharacterSubalgebra J : StarSubalgebra ℂ C(J → Circle, ℂ)`, the subalgebra generated by
  the `χ_n` (closed under `star` because `conj χ_n = χ_{-n}`).
- `IsTrivialOn K n : Prop`: `χ_n(w) = 1` for every `w ∈ K`, for a subgroup `K` of `J → Circle`.

## Results

- `torusCharacter_zero`, `torusCharacter_add`, `torusCharacter_neg`, `torusCharacter_inv`:
  `χ_0 = 1`, `χ_{m+n} = χ_m χ_n`, `χ_{-n} = conj χ_n`, `χ_n(z⁻¹) = conj(χ_n(z))`.
- `torusCharacter_single`: `χ_{e_i}(z) = z_i` for `e_i = Pi.single i 1`.
- `torusCharacterSubalgebra_coe`: the subalgebra generated by the `χ_n` is their linear span.
- `torusCharacterSubalgebra_separatesPoints`: it separates points.
- `span_torusCharacterMap_closure_eq_top` (**density of trigonometric polynomials**): the span
  of the `χ_n` is dense in `C(J → Circle, ℂ)` for the uniform norm.
- `integrable_mul_torusCharacter`: `f χ_n` is integrable for continuous `f`.
- `integral_torusCharacter` (**orthogonality**): `∫ χ_n dμ = μ(T)` if `n = 0`, else `0`.
- `torusFourierCoeff_tsum`: the Fourier coefficients of `z ↦ ∑_m c(m) conj(χ_m(z))` are
  `μ(T) c(n)`.
- `eq_zero_of_torusFourierCoeff_eq_zero` (**uniqueness**): a continuous function with all Fourier
  coefficients `0` is `0`.
- `hasSum_torusFourierCoeff_mul_conj` (**Fourier inversion**):
  `∑_n f̂(n) conj(χ_n(z)) = μ(T) f(z)` for every `z`, as an unconditionally convergent sum.
- `hasSum_torusFourierCoeff_mul_conj_of_isProbabilityMeasure`: the same with `μ(T) = 1`.
- `summable_one_add_abs_sq_inv`: `∑_{k ∈ ℤ} (1 + |k|)^{-2} < ∞`.
- `summable_prod_one_add_abs_sq_inv`: `∑_{n ∈ ℤ^J} ∏_j (1 + |n_j|)^{-2} < ∞`.
- `summable_norm_torusFourierCoeff`: the Fourier coefficients of a smooth function are
  absolutely summable.
- `hasSum_torusFourierCoeff_mul_conj_of_isSmooth`: Fourier inversion for smooth functions.
- `torusCharacter_mul_mem`: `χ_n(w₁ w₂) = χ_n(w₁) χ_n(w₂)` for `w₁, w₂ ∈ K`.
- `sum_torusCharacter_subgroup` (**orthogonality on a finite subgroup**):
  `∑_{w ∈ K} χ_n(w) = |K|` if `IsTrivialOn K n`, else `0`.
- `integral_mul_right_mul_torusCharacter`: `∫ f(z w) χ_n(z) dμ = f̂(n) conj(χ_n(w))`.
- `hasSum_torusFourierCoeff_mul_conj_isTrivialOn` (**inversion along a finite subgroup**): the
  sum of `f̂(n) conj(χ_n(z))` over the `n` with `IsTrivialOn K n` (the other terms are `0`) is
  `μ(T) |K|⁻¹ ∑_{w ∈ K} f(z w)`.

## Proof notes

1. Characters: coordinatewise identities in `Circle` (`zpow_add`, `zpow_neg`, `inv_zpow`,
   `Circle.coe_inv_eq_conj`).
2. Density: as for Mathlib's `mFourierSubalgebra` on `UnitAddTorus`. The adjoined set is closed
   under products and contains `χ_0 = 1`, so the algebra is the span
   (`Algebra.adjoin_eq_span_of_subset`); the characters `χ_{e_i}` are the coordinate functions,
   which separate points; Stone–Weierstrass gives density.
3. Orthogonality: for `n ≠ 0` choose `j` with `n_j ≠ 0`. The published translation identity with
   `f = 1` and `θ = π / n_j` gives `∫ χ_n dμ = -∫ χ_n dμ`.
4. `torusFourierCoeff_tsum`: `conj(χ_m) χ_n = χ_{n-m}`. The integrals of the norms are
   `|c(m)| μ(T)`, which are summable, so `integral_tsum_of_summable_integral_norm` exchanges sum
   and integral, and step 3 leaves the term `m = n`.
5. Uniqueness: `p ↦ ∫ h p dμ` is a continuous linear functional on `C(J → Circle, ℂ)` (bounded by
   `‖h‖ μ(T) ‖p‖`). It vanishes on every `χ_n`, hence on the closure of their span, which is
   everything by step 2. At `p = conj h` this gives `∫ |h|^2 dμ = 0`, so `h = 0` almost
   everywhere, hence everywhere because `h` is continuous and `μ` is positive on open sets.
6. Inversion: if `μ = 0` both sides vanish. Otherwise `μ` is positive on open sets
   (`isOpenPosMeasure_of_mulLeftInvariant_of_compact`). The series
   `g(z) = ∑_n f̂(n) conj(χ_n(z))` converges uniformly (`continuous_tsum`), so `g` is
   continuous; by step 4 its coefficients are `μ(T) f̂(n)`, the coefficients of `μ(T) f`; by
   step 5, `g = μ(T) f`.
7. Summability for smooth `f`: with `k = 2|J|` the published decay estimate gives
   `(1 + ‖n‖)^k |f̂(n)| ≤ C`. Since `1 + |n_j| ≤ 1 + ‖n‖`,
   `∏_j (1 + |n_j|)^2 ≤ (1 + ‖n‖)^k`, so `|f̂(n)| ≤ C ∏_j (1 + |n_j|)^{-2}`. The latter series
   converges: its partial sum over a finite set `S` is at most the sum over the box
   `∏_j {n_j : n ∈ S}`, which factors (`Finset.prod_univ_sum`) into a product of partial sums
   of the convergent one-variable series (comparison with `∑ 1/k^2`).
8. Finite subgroup: `∑_{w ∈ K} χ_n(w)` is unchanged by multiplying all `w` by some `w₀ ∈ K`,
   so it vanishes when `χ_n(w₀) ≠ 1` for some `w₀`. Right translation invariance of `μ`
   (`integral_mul_right_eq_self`) gives `integral_mul_right_mul_torusCharacter`. For
   `F(z) = ∑_{w ∈ K} f(z w)` the coefficients are `F̂(n) = |K| f̂(n)` if `IsTrivialOn K n` and
   `0` otherwise; they are summable, and step 6 applied to `F`, divided by `|K|`, gives the
   result.

## Relation to the Library

`TorusFourierDecay` proves the decay of the coefficients used in step 7; this module adds
orthogonality, uniqueness and inversion. `DiscreteFourierUniqueness` works on Mathlib's
`UnitAddTorus d` with the additive characters `mFourier` and proves that an absolutely summable
function on `ℤ^d` (or on a finitely generated abelian group) whose character sums vanish is `0`;
it does not invert Fourier series of functions on the torus. Mathlib's
`UnitAddTorus.hasSum_mFourier_series_apply_of_summable` is the inversion formula on
`UnitAddTorus d` for its Haar probability measure; the present module works directly on the
multiplicative torus `J → Circle` with an arbitrary finite invariant measure, as in the
Library's torus coordinates for `Im X(G)`. A search of the Library for `hasSum_mFourier`,
`torusFourierCoeff` and Stone–Weierstrass on `J → Circle` found no Fourier inversion there.

## Open obligations

Applying this to Proposition VII.2.1 requires: the identification of `Im X(G)` with
`J → Circle` and of the measure of I.1 with a finite invariant `μ` of mass `d_G`; the kernel
of `Im X(G) → Im X(A_G)` as a finite subgroup, and the identification of the characters
trivial on it with the image of `A_G` modulo `A_G ∩ K` for Waldspurger's `K` (Pontryagin
duality for the lattice); the quotient `𝒪 = Im X(G)/S` by the finite twist stabilizer `S`
(III.7) with its orbit measure (VI.3) and the resulting factor `|S|` described above; and the
remaining steps of the proof (unfolding over `A_G \ G`, Schur orthogonality III.1 (2), (3),
Lemma VII.1.1 (ii)).
