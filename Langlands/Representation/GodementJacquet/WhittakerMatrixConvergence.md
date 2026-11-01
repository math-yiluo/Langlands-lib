# Convergence of full-matrix Whittaker integrals

Module `Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence`,
namespace `Langlands.GodementJacquet.WhittakerTorus.Padic`.

Let `F` be a p-adic field with its canonical topological data (topology,
valuation, local field structure). `Fˣ`, `G = GL_(n+1)(F)` and its upper
unipotent subgroup `N` carry their Borel σ-algebras. Let `ψ` be a unitary
additive character of `F` and `W : G → ℂ` a function with
`IsWhittakerLike F ψ W`: continuous, left `(N, ψ)`-equivariant, right invariant
under an open subgroup, and with a torus expansion
`W(diag(a) k) = Σ_{χ ∈ X_k} φ_{k,χ}(a_0/a_1, …, a_(n-1)/a_n) χ(a)` for every
`k ∈ G` (finitely many finite functions `χ`, Schwartz–Bruhat coefficients
`φ_{k,χ}`). Let `Φ` be a Schwartz–Bruhat function on the full space of
`(n+1) × (n+1)` matrices.

The main theorem, `IsWhittakerLike.matrixConverges`, states: assuming
`FiniteFunctionMellinStatement`, there is a real `c` such that for every
complex `s` with `Re s > c`, the integrand `g ↦ Φ(g) W(g) |det g|^s` is
integrable for `generalLinearHaar` on `G`. In the Library's terms this is
`GodementJacquet.Padic.MatrixConverges F Φ s W`. The integral is unshifted;
the shift `n/2` of `ModelWhittakerRationalityStatement` only translates the
half-plane.

## Source and provenance

The content is internal and derived. It is the convergence half of a proof of
`ModelWhittakerRationalityStatement` from the torus expansion of Whittaker
functions and `FiniteFunctionMellinStatement`. Jacquet, Piatetski-Shapiro and
Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), Section
(5.2), printed pages 420–421, say that for a representation of Whittaker type
these integrals "converge for Re(s) large". That section completes results of
the same authors' *Automorphic forms on GL(3) I*, Ann. of Math. 109 (1979).
There, printed page 186 (proof of Proposition (3.1)), convergence comes from
majorizing `W` by a gauge (Section (2.3), printed page 183). The Lean proof
uses the Iwasawa decomposition `G = N A K`, a bound for the integral over `N`,
and then torus integrals, as in the convergence part of the proof of Theorem
(2.7) of the 1983 paper (printed page 392: the same reduction applied to
absolute values). The torus estimate is taken from
`FiniteFunctionMellinStatement` (through `torusMellin`), not from a gauge
bound. The helpers below are not stated separately in the literature.

The hypothesis `FiniteFunctionMellinStatement` is the published Library
statement in `Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement`.
The theorems here take it as an explicit hypothesis `hFFM`. Its Library proof
`Langlands.RankinSelberg.finiteFunctionMellin` (module
`Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`) can be
supplied for it.

## Declarations

The module reuses four helpers of `WhittakerMatrixRationality`.
`exists_common_halfPlane` (namespace `Langlands.GodementJacquet.WhittakerTorus`)
gives a common right half-plane for finitely many properties that each hold
on some right half-plane. `borelModulus_pos`,
`borelModulus_mul` and `continuous_borelModulus` (namespace `Padic` there)
say that the modulus
`δ(a) = ∏_{i<j} |a_i/a_j|` (`borelModulus`, from `WhittakerIwasawaReduction`)
is positive, multiplicative and continuous on the torus `(Fˣ)^(n+1)`.

The module also uses, unchanged, the box test function and the slice bound of
`WhittakerSliceBound` (same namespace), which do not depend on any hypothesis:
`normBox F n ρ` (the box `{x ∈ F^(n+1) | |x_i| ≤ ρ for all i}`), its
characteristic function `boxTest F n hρ`, with `boxTest_apply_of_le` (it is `1`
on the box), the monomial `torusMonomial F e a = ∏_i |a_i|^(-e_i)` with
`torusMonomial_nonneg`, `measurable_matrixIntegrand` (for continuous `W` the
integrand `g ↦ Φ(g) W(g) |det g|^s` is measurable), and `exists_slice_bound`.
The slice bound states that for `k ∈ G` there are `B`, `ρ > 0` and exponents `e`
with

`∫_N |Φ(u diag(a) k)| du ≤ B · ∏_i |a_i|^(-e_i) · 1_box(a)`

for all `a`, where `1_box` is `boxTest F n hρ`.

Declarations of this module (with the canonical local instances of a
`PadicField` and Borel σ-algebras on `Fˣ`, `G` and `N`):

- `torusWeight F e a = δ(a)⁻¹ · ∏_i |a_i|^(-e_i)`, as a complex number.
  `torusWeight_mul` shows it is multiplicative, and `continuous_torusWeight`
  that it is continuous. `isFiniteFunction_torusWeight`: it is a finite
  function. This uses `IsFiniteFunction.of_mul_apply` from
  `WhittakerTorusCoordinates`: a continuous function with
  `η(b a) = c(b) η(a)` is finite. `enorm_torusWeight` writes its extended norm
  as `ofReal (δ(a)⁻¹) · ofReal (∏_i |a_i|^(-e_i))`.
- `lintegral_torus_lt_top hFFM hW Φ hk`: for `k ∈ GL_(n+1)(O)`
  (`integralK F n`) there is a half-plane `Re s > c` on which

  `∫_A δ(a)⁻¹ ∫_N |Z(u diag(a) k)| du da < ∞`,

  with `Z = matrixIntegrand F Φ s W` and `da` the product of the
  multiplicative Haar measures on `Fˣ`. Proof:
  1. `lintegral_unipotent_matrixIntegrand` (from
     `WhittakerIwasawaReduction`) gives
     `∫_N |Z(u diag(a) k)| du = |W(diag(a) k) |det diag(a)|^s| · ∫_N |Φ(u diag(a) k)| du`.
     It uses `|ψ| = 1` and `det u = 1`.
  2. Bound the last factor by the slice bound.
  3. Expand `W(diag(a) k)` with the torus expansion for `k` (field
     `expansion`). Each summand is then the torus integrand
     `torusIntegrand F φ_χ J (χ · torusWeight F e) s a` of
     `WhittakerTorusMellin`, where `J = boxTest F n hρ`. The triangle
     inequality (`enorm_sum_le`) gives
     `δ(a)⁻¹ ∫_N |Z(u diag(a) k)| du ≤ B · Σ_{χ ∈ X} |torusIntegrand … s a|`.
  4. `χ · torusWeight F e` is a finite function, so `torusMellin` (with
     `FiniteFunctionMellinStatement`) makes each torus integrand integrable on
     a right half-plane. `exists_common_halfPlane` gives a common half-plane
     for the finitely many `χ ∈ X`.
  5. On that half-plane, `lintegral_const_mul'` and `lintegral_finsetSum'`
     reduce the bound to `B` times a finite sum of finite integrals.
- `IsWhittakerLike.matrixConverges hFFM hW Φ` (**main theorem**). Proof:
  1. Measurability is `measurable_matrixIntegrand`. It remains to show that
     `∫_G |Z| < ∞`.
  2. `lintegral_iwasawa` (from `WhittakerIwasawaReduction`) rewrites
     `∫_G |Z|` as `∫_K ∫_A δ(a)⁻¹ ∫_N |Z(u diag(a) k)| du da dk` over
     `K = GL_(n+1)(O)`.
  3. `IsWhittakerLike.exists_cosetSum` gives an open subgroup `K₀ ≤ K` that
     leaves `Z` right invariant, and a finite set `S ⊆ K` with
     `∫_K f = Σ_{k ∈ S} μ(K₀) f(k)` for every right `K₀`-invariant `f`. The
     function `k ↦ ∫_A δ(a)⁻¹ ∫_N |Z(u diag(a) k)|` is right `K₀`-invariant
     because `Z` is (rewrite `u diag(a) k k₀ = (u diag(a) k) k₀`).
  4. `μ(K₀) ≤ μ(K) = 1` (`generalLinearHaar_integralSubgroup`), so it is
     finite. `lintegral_torus_lt_top` makes each of the finitely many terms
     `k ∈ S` finite on a half-plane, and `exists_common_halfPlane` gives a
     common one.
