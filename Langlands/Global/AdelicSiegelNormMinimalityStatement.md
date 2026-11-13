# Polynomial norm minimality on actual adelic Siegel products

Author: Worker 5152.

`Langlands.Global.AdelicSiegelFactors.SiegelNormMinimalityStatement` is a target
proposition for proof. This module states it and proves nothing about it. It is
property (vii) of Mœglin–Waldspurger I.2.2 for the Library's Siegel products and
heights, in a polynomial form.

## The statement

The proposition is universally quantified, in universe `u`, over:

- a number field `F : Type u` and a group scheme `G` over `Spec F` with
  `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, the interfaces of
  `AdelicSiegelReductionStatement`;
- a natural number `N` and a matrix representation
  `rho : GroupScheme.MatrixRepresentation G (Fin N)`.

It assumes three things: `IsConnectedReductive G`, `IsClosedSubgroup rho` and
`0 < N`. Then, for every actual algebraic Siegel setup
`T, i, ν, T₀, j` with `IsSiegelAlgebraicSetup F G T i ν T₀ j` (module
`AdelicSiegelReductionStatement`), every
`C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)`
and every threshold `t : ℝ≥0ˣ`, it asserts:

there are a real `c` and a natural number `e` such that for every point `s` of the
weak Siegel product
`weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t` and every
rational point `q : RationalGroupPoints F G`,

```text
adelicHeight F G rho s ≤ c * adelicHeight F G rho (rational F G q * s) ^ e.
```

Here:

- the weak Siegel product (module `AdelicSiegelFactors`) is the set of products
  `ι_N(n) · ι_M(m) · positiveMap(a) · k`. The factors are `n` in the compact set
  `C.omegaN` of points of the canonical standard unipotent group, `m` in the compact
  set `C.omegaM` of norm-one points of the canonical standard Levi, `a` in the
  intrinsic positive points of `T₀` with `t ≤ |α(a)|` for every simple relative root
  `α` (`PositiveRealTorus.weakSimpleRootChamber`), and `k` in the compact subgroup
  `C.compactSubgroup`;
- `adelicHeight` (module `AdelicRepresentationHeight`) is the full local-product
  matrix-and-inverse height of `rho`, scaled by `N` at the infinite places;
- the rational point acts on the left through `AdelicGroupPoints.rational`.

`c` and `e` may depend on everything except `s` and `q`. The compact data `C` are
arbitrary: no maximality, Iwasawa property or covering is assumed, and the
statement says nothing about whether the product covers `G(𝔸)¹`.

## Meaning and expected proof

MW I.2.2 (vii) says that points of a Siegel set are almost minimal for the height in
their `G(F)`-orbit. MW prove it on printed p. 21. The same argument works for the
Library's products, with these steps.

1. **Moving the compact factors.** `m` commutes with `positiveMap(a)`, since the
   standard Levi is the centralizer of `T` (setup clause
   `standardLevi i ν ∅ = torusCentralizer i`). Conjugation by `positiveMap(a)⁻¹`
   multiplies each coordinate of the unipotent group by `w(a)⁻¹` for a positive
   relative root `w`; the published proof `positiveTorusTriangularCoordinates`
   supplies such coordinates. On the chamber `t ≤ |α(a)|` these factors are bounded,
   so `positiveMap(a)⁻¹ ι_N(n) positiveMap(a)` stays in a compact set. Hence
   `s = positiveMap(a) · b` with `b` in a fixed compact set, and
   `adelicHeight(s)` and `adelicHeight(q s)` are within bounded factors of
   `adelicHeight(positiveMap(a))` and `adelicHeight(q · positiveMap(a))`. The
   Library's `adelicHeight_mul_le` and `adelicHeight_inv` give this.
2. **The diagonal inequality.** The split torus `T₀` acts through `rho` by
   characters in a rational basis. In that basis `positiveMap(a)` is diagonal with
   positive entries `χ_l(a)` that are equal at all infinite places and `1` at the
   finite places. Fix any column of the rational matrix `rho(q)`. One of its entries
   `x` is nonzero, and the product formula gives `∏_v |x χ_l(a)|_v = |χ_l(a)|_𝔸`.
   The same holds for a row of the inverse. Together these give
   `adelicHeight(q · positiveMap(a)) ≥ c' · adelicHeight(positiveMap(a))`. MW reach
   the same inequality through the Bruhat decomposition.

This argument gives the linear bound `e = 1`, as in MW. The statement asks only for
a polynomial bound, which is all that `adelicRationalHeightReductionStatement_of_siegel`
(module `AdelicRationalHeightReduction`) needs. The argument does not use that
`rho` is a closed embedding; the hypothesis is kept because the consumer has it.

## Use

`Langlands.Global.RepresentationGrowth.adelicRationalHeightReductionStatement_of_siegel`
(module `AdelicRationalHeightReduction`) combines this statement with the Siegel
covering `AdelicSiegelReductionStatement` and the central-factor statement
`CentralNormOneHeightFactorStatement`. The result is
`AdelicRationalHeightReductionStatement`, which in turn gives the slice-to-global
growth comparison `AdelicSliceModerateGrowthStatement`.

## Original-source correspondence

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (printed page `p` is PDF
page `p - 17`).

- I.2.1 (printed p. 20, PDF p. 3): Siegel sets `S = {p a k : p ∈ ω, a ∈ A_{M₀}(t₀),
  k ∈ K}` with `ω ⊂ P₀` compact and `A_{M₀}(t₀) = {a : a^α > t₀ for every simple α}`.
- I.2.2 (printed pp. 20–21, PDF pp. 3–4): the height through `i_G : G → SL_{2n}` and
  property (vii): there is `c > 0` with `‖g‖ ≤ c ‖γ g‖` for every `γ ∈ G(k)` and
  `g ∈ S`. The proof is on printed p. 21. It moves `ω` and `K` aside, conjugates
  `i_G(T₀)` to the diagonal torus and proves `‖a‖ ≤ ‖γ a‖` for `GL_n` with the Bruhat
  decomposition and the product formula.

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations` (PDF page = printed page + 17), §2.7,
(2.25)–(2.26), printed p. 71 (PDF p. 88): the weak Siegel product with rational points on the
left and the inequality `t ≤ |α(a)|`. This is the Library's `weakSiegelProduct`.

## Provenance

The statement is derived from MW I.2.2 (vii). It differs from the printed statement
in four ways, each of which weakens or transports it:

- the set is the Library's ordered weak Siegel product
  `Ω_N Ω_M A_{T₀}(t) K`. Here `Ω_N Ω_M` is a compact subset of `P₀(𝔸)`, and
  `A_{T₀}(t)` is the chamber part of the positive points of the derived split torus.
  Each such product lies in an MW Siegel set enlarged by a compact set on the
  right;
- `K` is any compact subgroup, not MW's fixed maximal compact subgroup;
- the height is the Library's `adelicHeight` of a given closed `rho`, not MW's
  height for an embedding into `SL_{2n}`;
- the bound is polynomial rather than linear.
