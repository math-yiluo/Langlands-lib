# Iwasawa reduction of full-matrix Whittaker integrals

Module `Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction`,
namespace `Langlands.GodementJacquet.WhittakerTorus.Padic`.

Let `F` be a p-adic field with its canonical topological data (topology,
valuation, local field structure). `Fˣ`, `G = GL_(n+1)(F)` and its upper
unipotent subgroup `N` carry their Borel σ-algebras. `dg` is
`generalLinearHaar` (mass one on `K = GL_(n+1)(O)`), `du` is `unipotentHaar`
and `da` is the product of the normalized multiplicative Haar measures on
`A = (Fˣ)^(n+1)`. Write `|·|` for the normalized absolute value, `ψ_N` for the
standard character of `N` attached to `ψ`, and
`Z(g) = Φ(g) W(g) |det g|^s` for the full-matrix integrand
(`GodementJacquet.Padic.matrixIntegrand F Φ s W`).

The module sets up the reduction of `∫_G Z(g) dg` to torus integrals. It defines
the analytic properties of `W` that the reduction uses. It proves the Iwasawa
integration formula in this normalization, the factorization of `Z` at
`u diag(a) k`, the unipotent integral of `Z` and of `|Z|`, and the reduction of
the `K`-integral to a finite sum.

## Source and provenance

The content is internal and derived. It is the first part of a proof of
`ModelWhittakerRationalityStatement` from the torus expansion of Whittaker
functions and `FiniteFunctionMellinStatement`. Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), Section (5.2), printed pages
420–421, assert this for a representation `σ` of Whittaker type acting on its
Whittaker model: the full-matrix integrals "converge for Re(s) large, define
rational functions of X = q^(-s)". That section completes results of the same
authors' *Automorphic forms on GL(3) I*, Ann. of Math. 109 (1979). There,
printed page 186 (proof of Proposition (3.1), for irreducible generic
representations), convergence comes from majorizing `W` by a gauge and
rationality from the identity (3.1.4) with matrix coefficients. The route
formalized here is different: it adapts the proof of Theorem (2.7) of the
1983 paper, printed pages 391–392, from the Rankin–Selberg integrals to the
full-matrix integrals. That proof uses the Iwasawa decomposition, the
coordinates (4), the torus expansion of Whittaker functions, and the Mellin
integrals (5)–(6). In the full-matrix
case, the integral `x ↦ ∫_N Φ(u diag(x) k) ψ_N(u) du` is a Schwartz–Bruhat
function of the diagonal entries (used in
`integral_unipotent_matrixIntegrand`); in the Rankin–Selberg case of the 1983
proof, the test function enters only through `Φ(a_r)`. The predicate
`IsWhittakerLike` and its field `expansion` are packaging for this
formalization. For the coefficient model, the later module
`WhittakerModelRationality` derives them from the Library predicate
`RankinSelberg.CoefficientTorusExpansion` (module
`RankinSelberg.ModelAsymptoticStatement`).

## Declarations

- `integralK F n`: the integral subgroup `K = GL_(n+1)(O)`
  (`Conductor.integralSubgroup`), as an abbreviation.
- `borelModulus F a`: the upper-Borel modulus `δ(a) = ∏_{i<j} |a_i / a_j|`.
- `HasTorusExpansion F f`: for a function `f` on `A`, there are a finite set
  `X` of finite functions on `A` (`IsFiniteFunction`: continuous, with
  finite-dimensional span of left translates) and Schwartz–Bruhat functions
  `φ_χ` on `F^n` with
  `f(a) = Σ_{χ ∈ X} φ_χ(a_0/a_1, …, a_(n-1)/a_n) · χ(a)` for all `a`.
- `IsWhittakerLike F ψ W`: a structure with four fields.
  1. `continuous`: `W` is continuous.
  2. `equivariant`: `W(u g) = ψ_N(u) W(g)` for `u ∈ N`.
  3. `smooth`: `W` is right invariant under some open subgroup.
  4. `expansion`: for every `k ∈ G`, `a ↦ W(diag(a) k)` has a torus expansion.
- `lintegral_iwasawa F f hf`: for measurable `f : G → [0, ∞]`,
  `∫_G f dg = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk`. Proof:
  `IwasawaHaar.lintegral_generalLinearHaar` with weight `δ(a)⁻¹`. Its
  hypothesis on `diag(a)`-conjugation of `du` is `diagonalConj_map` together
  with `singleton_modulus_real`.
- `integral_iwasawa F f hf`: the same formula for integrable complex `f`
  (Bochner integrals). This is `IwasawaHaar.integral_generalLinearHaar_iwasawa`
  for the canonical data, with `δ` named.
- `normalizedAbs_det_integralK`: `|det k| = 1` for `k ∈ K`
  (`normalizedAbs_det_of_mem_integralSubgroup`).
- `matrixIntegrand_iwasawa`: if `W(u g) = ψ_N(u) W(g)` and `k ∈ K`, then
  `Z(u diag(a) k) = (W(diag(a) k) · |∏ a_i|^s) · (Φ(u diag(a) k) · ψ_N(u))`.
  Proof: `det u = 1` (`determinantWeight_unipotent_mul`),
  `det diag(a) = ∏ a_i` and `|det k| = 1`.
- `integral_unipotent_matrixIntegrand`: for `k ∈ K`,
  `∫_N Z(u diag(a) k) du = W(diag(a) k) · |∏ a_i|^s · J_k(a)`. Here
  `J_k = WhittakerSlice.sliceIntegral F ψ (Φ(· k))` is the slice integral
  `x ↦ ∫_N Φ(u diag(x) k) ψ_N(u) du`. It is Schwartz–Bruhat on `F^(n+1)` by
  `sliceIntegral_rightTranslate_mem`. Proof: pull the constant factor out of
  the integral (`integral_const_mul`).
- `lintegral_unipotent_matrixIntegrand`: for `k ∈ K`,
  `∫⁻_N |Z(u diag(a) k)| du = |W(diag(a) k) · |∏ a_i|^s| · ∫⁻_N |Φ(u diag(a) k)| du`,
  using `|ψ_N(u)| = 1` (`norm_standardCharacter`) and `lintegral_const_mul'`.
- `matrixIntegrand_mul_right`: if `k₀ ∈ K`, `Φ(M k₀) = Φ(M)` for all matrices
  `M` and `W(g k₀) = W(g)` for all `g`, then `Z(g k₀) = Z(g)`.
- `IsWhittakerLike.exists_cosetSum`: for `W` with `IsWhittakerLike F ψ W` and a
  test function `Φ`, there are an open subgroup `K₀ ≤ K` and a finite set
  `S ⊆ K` with three properties.
  1. `Z(g k₀) = Z(g)` for all `s`, `g` and `k₀ ∈ K₀`.
  2. `∫⁻_K f dg = Σ_{k ∈ S} vol(K₀) f(k)` for every `f : G → [0, ∞]` with
     `f(k k₀) = f(k)` for `k ∈ K` and `k₀ ∈ K₀`.
  3. The same identity holds for Bochner integrals of complex `f`, with the
     real mass of `K₀`.

  Proof: `CosetSum.Padic.exists_openSubgroup_rightInvariant` gives `K₀`, using
  the field `smooth`. Then `CosetSum.exists_cosetSum` for the Haar measure `dg`
  and the compact subgroup `K` (`CosetSum.Padic.isCompact_integralSubgroup`)
  gives `S`, and `matrixIntegrand_mul_right` gives property 1.
