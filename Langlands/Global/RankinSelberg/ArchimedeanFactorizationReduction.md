# A conditional reduction of the unequal-rank factorization over `S` and the infinite places

Module `Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`. Author: Worker 394.

## 1. Content and provenance

The published statement
`Langlands.Global.RankinSelbergGlobal.UnequalArchimedeanFactorizationStatement.{u, uQ}`
(module [`ArchimedeanFactorizationStatement`](ArchimedeanFactorizationStatement.md), called
(U) here) is the unequal-rank conjunct of `ArchimedeanFactorizationStatement`, the target of
Task 7397. It says that, for suitable vectors `x`, `x'` spherical outside `S`, the partial
global integrals `Ψ_(S∪∞)(s; W, W')` and `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃')` are one constant
`c ≠ 0` times the product of archimedean local integrals and local integrals at the places of
`S`, and that none of these local factors vanishes identically on a right half-plane.

This module contains:

* helper definitions (Section 2): the local components of an adelic point, of a class in
  `N(𝔸) \ GL(𝔸)` and of an adelic rectangular matrix, the set of adelic rectangular matrices
  integral outside `S`, p-adic integrals in the conventions of `PadicUnequalTestData`, and two
  accessors for the measure field of `PadicUnequalTestData`;
* three new Prop-valued premises (Section 3): `UnipotentClassProductStatement` (B),
  `RectangleTateStatement` (C) and `UnequalPointwiseFactorizationStatement` (A_U);
* the statement `UnequalArchimedeanFactorizationReductionStatement.{u, uQ}` (Section 4):
  A_U, B and C together imply (U);
* the theorem `unequalArchimedeanFactorizationReduction`, which proves it (Section 5).

The theorem is a reduction. It does not prove (U), and its three premises are open. It is an
intermediate result of Task 7397 in the sense of the "Intermediate results" section of that
task's revision 1. The task's required result, a proof of `ArchimedeanFactorizationStatement`,
stays open. The equal-rank conjunct is not treated here.

**Source of the reduction.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in
Bernstein–Gelbart (eds.), *An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), proof of Theorem 4.1,
printed p.219 (PDF p.222). For factorizable cusp forms the global Whittaker functions are
products of local ones (p.206), the partial integral over `S ∪ ∞` is then the product of the
local integrals over `S ∪ ∞`, and the inner rectangular integral of the dual integral
factors through Tate's local measures. The Markdown of (U) (section "Why it holds") gives the
same argument in the Library's conventions.

**Provenance (internal).** The decomposition into premises is ours. It separates Cogdell's
argument into three parts:

* A_U, the representation theory: pure tensors, their local Whittaker functions, the
  unramified places and nonvanishing. It is stated pointwise, on the classes over which the
  partial integral runs, so that it contains no integration;
* B, measure theory on `N(𝔸) \ GL(𝔸)`: the product structure of the partial domain;
* C, Tate's measure theory on adelic rectangular matrices.

The Lean proof combining them is integration bookkeeping only.

The module declares the two local instances of (U) (the Library theorems
`GroupScheme.GeneralLinear.isAffine_groupScheme` and `GroupScheme.GeneralLinear.smoothStatement`
made available to instance search). It also makes the following Library instances local
instances: `rectangleMeasurableSpace` and `rectangleBorelSpace` (Borel structure on adelic
rectangular matrices, from `WhittakerIntegrals`), and the twelve Borel measurable-space
instances `ArchimedeanLocal.archimedean{Real,Complex}{Q,GL,N}{Measurable,Borel}` on the real
and complex groups `GL_(t+1)`, `N_(t+1)` and quotients `N_(t+1) \ GL_(t+1)` (from
`ArchimedeanIntegrals`). These are the measurable structures used by the statements of (U),
and they add no hypothesis.

## 2. Helper definitions

Throughout, `F` is a number field, `n = r + 1`, `m = t + 1`, and `S` is a finite set of finite
places.

### 2.1 Local components

* `archimedeanComponent F n g : ArchimedeanGL F n`: the archimedean component `g_∞` of an
  actual adelic point `g : Points F n`, in the mixed coordinates
  `GL_n(ℝ^(r₁) × ℂ^(r₂))` (Library maps `GeneralLinearGroupPoints.adelicEquiv`,
  `AdelicGL.infinite`, `archimedeanGLCoordinates`).
* `realComponent F n v g : GL_n(ℝ)` for a real place `v`, and `complexComponent F n w g :
  GL_n(ℂ)` for a complex place `w`: the entrywise projection of `g_∞` to the coordinate `v`
  of the real factor, resp. `w` of the complex factor, of the mixed space. These are the
  coordinates in which `IsRealPlaceWhittaker` and `IsComplexPlaceWhittaker` (module
  `ArchimedeanPlaces`) describe the archimedean restrictions of a global Whittaker function.
* `realQuotientProjection F t v q`, `complexQuotientProjection F t w q`,
  `finiteQuotientProjection F t v q`: for `q : WhittakerQuotient F (t + 1)`, a class in
  `N_m(𝔸) \ GL_m(𝔸)`, the class in the local quotient `LeftUnipotentQuotient t K` (that is,
  `N_m(K) \ GL_m(K)`) of the corresponding component of the representative `q.out`. At a
  finite place the component is the Library's `finiteComponent F (t + 1) v`, and `K` is the
  carrier of `padicField v`. The local class does not depend on the representative, since
  two representatives differ by an element of `N_m(𝔸)` on the left, whose components lie in
  `N_m(K)`; the definitions use `q.out` and need no such fact.
* `realRectCoordinates F v x`, `complexRectCoordinates F w x`, `localRectCoordinates F v x`:
  the entrywise coordinates at `v` (or `w`) of an adelic matrix
  `x ∈ M_(k,m')(𝔸)`, through the mixed coordinates
  `InfiniteAdeleRing.ringEquiv_mixedSpace` at the infinite places and through
  `finiteProjection F v` at the finite places.
* `rectIntegralOutside F k m' S`: the adelic matrices whose entries lie in `𝒪_v` (Mathlib's
  `v.adicCompletionIntegers F`) at every finite place `v ∉ S`.

### 2.2 p-adic integrals

For a p-adic field `K : PadicField p` (canonical topology, Borel structures), as in the
fields of `PadicUnequalTestData`:

* `PadicQuotientMeasure K t`: the type of measures on `N_m(K) \ GL_m(K)` for the Borel
  structure of the canonical topology, the type of the `measure` field of
  `PadicUnequalTestData`.
* `padicQuotientIntegral K μ f = ∫ f dμ` for `f` on `N_m(K) \ GL_m(K)`.
* `padicRectIntegral K k m' ν f = ∫ f d(rectangularMeasure ν k m')` for `f` on `M_(k,m')(K)`,
  `ν` a `LocalAdditiveHaarMeasure` of `K` and `rectangularMeasure` the Library's entrywise
  product measure.
* `padicBlockIntegral K k μ ν f = ∫_(N\GL) ∫_(M_(k,m)) f(q, x) dx dq`, the rectangular
  variable integrated first.
* `IsCompatiblePadicQuotientMeasure K μ`: the unipotent Haar measure `unipotentHaar K.Carrier t`
  is right invariant and `μ` is compatible (`QuotientIntegration.IsCompatible`) with the
  Library's `generalLinearHaar K.Carrier t` and `unipotentHaar K.Carrier t`: `μ ≠ 0`, `μ` is
  regular, invariant under right translations, and satisfies the Weil integration formula for
  continuous compactly supported functions. This is the condition met by the fields
  `invariant` and `compatible` of `PadicUnequalTestData`.
* `PadicUnequalTestData.quotientMeasure D`, `PadicUnequalTestData.isCompatible_quotientMeasure
  D`: the `measure` field of the test data `D`, read as a `PadicQuotientMeasure`, and its
  compatibility. They only unfold the instances under which the fields are stated.

## 3. The premises

All three premises quantify over a number field `F : Type u`. For C and A_U the binders are
those of (U): `ψ` a `UnitaryAdditiveCharacter (Adeles F)` trivial on `F`, `S` with
`FiniteAdditiveSupport ψ S` (the canonical component `ψ_v` has conductor `0` at every finite
`v ∉ S`), the archimedean components `aR v`, `aC w` of `ψ` (`IsRealAdditiveComponent`,
`IsComplexAdditiveComponent`), canonical finite components `ψv v` (`IsCanonicalFiniteAdditiveComponent`)
and measures `νv v` self-dual for them (`IsSelfDualMeasure`).

### 3.1 Premise B: `UnipotentClassProductStatement.{u}`

For every `F`, `t`, `S`, quotient measure data `DR v : RealQuotientMeasureData t` at the real
places, `DC w : ComplexQuotientMeasureData t` at the complex places, and measures `μS v` on
`N_m(F_v) \ GL_m(F_v)` for `v ∈ S` satisfying `IsCompatiblePadicQuotientMeasure`, there is a
constant `C ≠ 0` such that for all functions `fR v`, `fC w`, `fS v` on the local quotients,

```text
∫_(unipotentIntegralClasses F m S) ∏_v fR v (q_v) · ∏_w fC w (q_w) · ∏_(v ∈ S) fS v (q_v) d(whittakerQuotientMeasure F m)
  = C · ∏_v ∫ fR v d(DR v).measure · ∏_w ∫ fC w d(DC w).measure · ∏_(v ∈ S) ∫ fS v dμS v,
```

where `q_v` is `realQuotientProjection`, `complexQuotientProjection` or
`finiteQuotientProjection`. `unipotentIntegralClasses F m S` (module
`PartialIntegralExhaustion`) is the set of classes `q` with `q.out_v ∈ N_m(F_v) GL_m(𝒪_v)` at
every finite `v ∉ S`, the domain of the partial integrals.

**Why it holds.** Let `U_S = unipotentIntegralClasses F m S`, `G_v = GL_m(F_v)`,
`N_v = N_m(F_v)`, `K_v = GL_m(𝒪_v)`. Since `N_m(𝔸) ∩ ∏_(v ∉ S) K_v` is `∏_(v ∉ S) N_m(𝒪_v)`,
the map `q ↦ ((q_v)_(v ∈ S ∪ ∞), (class of q.out_v)_(v ∉ S))` identifies `U_S` with

```text
∏_(v ∈ S ∪ ∞) N_v \ G_v  ×  ∏_(v ∉ S) N_m(𝒪_v) \ K_v,
```

a homeomorphism onto a product of homogeneous spaces whose second factor is compact.
`whittakerQuotientMeasure F m` is the image of the Haar quotient measure on
`N_m(F) \ GL_m(𝔸)` under the proper map to `N_m(𝔸) \ GL_m(𝔸)`, a nonzero right-invariant
Radon measure. Restricted to the open set `U_S` it is invariant under
`∏_(v ∈ S ∪ ∞) G_v × ∏_(v ∉ S) K_v`. Each `(DR v).measure`, `(DC w).measure`, `μS v` is a
nonzero regular right-invariant measure (`IsCompatible`), and the invariant measure on each
homogeneous space is unique up to a positive scalar. So the restriction is a positive constant
times the product of these measures and of the invariant probability measure on
`∏_(v ∉ S) N_m(𝒪_v) \ K_v`. The constant is positive because `U_S` is a nonempty open set and
the measure is invariant with full support. Since the integrand depends only on the
coordinates at `S ∪ ∞`, Fubini for products of functions of separate variables
(Mathlib's `integral_prod_mul`, which needs no integrability hypothesis) gives the identity,
for every choice of functions. The premise is not formalized here: the Library does not yet
contain this decomposition of `N(𝔸) \ GL(𝔸)` or the uniqueness of invariant measures on the
local quotients.

### 3.2 Premise C: `RectangleTateStatement.{u}`

For every `F` with `CompactSpace (AdeleQuotient F)`, `ψ`, `S`, `aR`, `aC`, `ψv`, `νv` as above,
every `k`, `m'` and all functions `hR v`, `hC w`, `hS v` on the local matrix spaces
`M_(k,m')(F_v)`,

```text
∫ 1_(rectIntegralOutside F k m' S)(x) · ∏_v hR v (x_v) · ∏_w hC w (x_w) · ∏_(v ∈ S) hS v (x_v) d(rectangleMeasure F k m')(x)
  = ∏_v ∫ hR v d(rectangularMeasure (realSelfDualMeasure (aR v)) k m')
    · ∏_w ∫ hC w d(rectangularMeasure (complexSelfDualMeasure (aC w)) k m')
    · ∏_(v ∈ S) padicRectIntegral (padicField v) k m' (νv v) (hS v),
```

with constant exactly one. `rectangleMeasure F k m'` is the Library's Haar measure on
`M_(k,m')(𝔸)` giving `M_(k,m')(F) \ M_(k,m')(𝔸)` volume one, `realSelfDualMeasure a` and
`complexSelfDualMeasure a` are the measures self-dual for `realScaledCharacter a` and
`complexScaledCharacter a` (module `ArchimedeanIntegrals`), and `x_v` is
`realRectCoordinates`, `complexRectCoordinates` or `localRectCoordinates`.

**Why it holds.** The product over all places of the measures self-dual for the components
of `ψ` is a Haar measure on `𝔸` which is self-dual for `ψ` and gives `F \ 𝔸` volume one,
because `ψ` is trivial on `F` (Tate's thesis, `tate-1967-thesis`, Theorems 4.1.1 and 4.1.2,
printed p.328, and Theorem 4.1.3(2), printed pp.330–331, PDF pp.173–174). So its `km'`-fold
product equals `rectangleMeasure F k m'`, both being Haar measures of covolume one for the
lattice `M_(k,m')(F)`. At a finite `v ∉ S` the conductor of `ψ_v` is `𝒪_v`, so the self-dual
measure gives `𝒪_v` volume one (Tate, §2.2, printed p.310). The set `rectIntegralOutside`
is the open subgroup `∏_(v ∈ S ∪ ∞) M_(k,m')(F_v) × ∏_(v ∉ S) M_(k,m')(𝒪_v)`, on which the
measure is the product of the local measures, the factor `∏_(v ∉ S) M_(k,m')(𝒪_v)` having
mass one. As in B, `integral_prod_mul` then gives the identity for every choice of functions.
The premise is not formalized here.

### 3.3 Premise A_U: `UnequalPointwiseFactorizationStatement.{u, uQ}`

Under exactly the binders of (U) (`F`, `ψ`, `t < r`, the cuspidal realizations `T`, `Td`,
`T'`, `Td'` with their contragredient hypotheses, spectral presentations `P`, `P'` with
irreducible admissible components, `S ⊇ P.exceptional ∪ P'.exceptional` with
`FiniteAdditiveSupport ψ S`, `aR`, `aC`, the archimedean parameters, `ψv`, `νv`), there exist
`x ∈ T.Space` and `x' ∈ T'.Space` spherical outside `S` such that, with `W`, `W'`,
`Wdual = ρ(w_(n,m)) W̃`, `W'dual = W̃'` defined exactly as in (U), there exist

* `κ ∈ ℂ`;
* archimedean functions `WR v`, `WR' v`, `WC w`, `WC' w` and quotient measure data `DR v`,
  `DC w`, of the types in (U);
* test data `D v : PadicUnequalTestData` at `v ∈ S`, of the type in (U);
* for `v ∈ S` and `s ∈ ℂ`, functions `fS v s` on `N_m(F_v) \ GL_m(F_v)` and `gS v s` on
  `N_m(F_v) \ GL_m(F_v) × M_(r-t-1,m)(F_v)`;

with

1. `κ ≠ 0`;
2. the `IsRealPlaceWhittaker` and `IsComplexPlaceWhittaker` conditions of (U) for `WR`, `WR'`,
   `WC`, `WC'`;
3. for `v ∈ S` and every `s`: `padicQuotientIntegral (D v).quotientMeasure (fS v s) =
   (D v).integral h (νv v) s` and `padicBlockIntegral (r - t - 1) (D v).quotientMeasure (νv v)
   (gS v s) = (D v).dualIntegral h (νv v) s`;
4. for every `s` and every `q ∈ unipotentIntegralClasses F m S`:
   `unequalWhittakerIntegrand F h W W' s q` equals
   `κ · ∏_v realUnequalIntegrand h (WR v) (WR' v) s (q_v) · ∏_w complexUnequalIntegrand h (WC w) (WC' w) s (q_w) · ∏_(v ∈ S) fS v s (q_v)`;
5. for every `s`, every `q ∈ unipotentIntegralClasses F m S` and every
   `y ∈ M_(r-t-1,m)(𝔸)`: `dualWhittakerKernel F h Wdual W'dual s q y` equals `κ` times
   `1_(rectIntegralOutside)(y) · ∏_v realUnequalDualKernel h (WR v) (WR' v) s (q_v, y_v) · ∏_w complexUnequalDualKernel h (WC w) (WC' w) s (q_w, y_w) · ∏_(v ∈ S) gS v s (q_v, y_v)`;
6. the four nonvanishing conclusions of (U), word for word: for every `a ∈ ℝ` there is `s`
   with `a < Re s` at which the archimedean product `Ψ_∞(s)`, resp. the dual product
   `Ψ̃_∞(s)`, resp. `(D v).integral h (νv v) s`, resp. `(D v).dualIntegral h (νv v) s`
   (each `v ∈ S`), is nonzero.

`unequalWhittakerIntegrand F h W W' s q = W(pad g) W'(g) |det g|^(s − (r−t)/2)` and
`dualWhittakerKernel F h W W' s q y = W(rectangularPoint g y) W'(g) |det g|^(s − (r−t)/2)`,
`g = q.out`, are the Library's global integrands (module `WhittakerIntegrals`), and
`realUnequalIntegrand`, `realUnequalDualKernel` and their complex analogues are the
archimedean integrands of `ArchimedeanIntegrals`; the dual kernels already contain the local
dual `ρ(w_(n,m)) W̃_v`, `W̃'_v` of their arguments.

**Why it holds.** This is Cogdell's choice of "appropriate" `φ`, `φ'` (p.219), made explicit
in the Markdown of (U), section "Why it holds".

* Take `x`, `x'` pure tensors, so `W(g) = ∏_v W_v(g_v)` and `W'(g) = ∏_v W'_v(g_v)` for all
  `g` (Cogdell p.206), with `W_v`, `W'_v` the normalized spherical Whittaker functions for
  `v ∉ S ∪ ∞` (`W_v(1) = 1`), unramified because `S` contains the exceptional sets.
* The archimedean `WR v`, `WC w` are nonzero multiples `λ_v W_v` of the local Whittaker
  functions (the restrictions of `IsRealPlaceWhittaker`), the constants being absorbed in `κ`.
  The local dual of `λ_v W_v` is `λ_v W̃_v`, so the same `κ` serves the dual kernel.
* At `v ∈ S`, `D v` records the local Whittaker functions of `x`, `x'` at `v`, and `fS v s`,
  `gS v s` are the local integrands of `D v`. The local integrals `(D v).integral` and
  `(D v).dualIntegral` are iterated integrals over the quotient and then the rectangular
  variable (`unequalRankIntegral`, module `QuotientIntegrals`), so clause 3 holds for every
  `s`, with no integrability condition.
* At a finite `v ∉ S` and `g_v = n k ∈ N_v K_v`, the local factor of the integrand is
  `ψ_v(n) W_v(1) · ψ_v(n)⁻¹ W'_v(1) · |det k|^(…) = 1`. The local integrands are
  left `N_v`-invariant, so they are functions of the class `q_v`, which is how clauses 4
  and 5 evaluate them.
* In the dual kernel, at a finite `v ∉ S`, the factor is `1_(M_(r-t-1,m)(𝒪_v))(y_v)`: for
  integral `y_v` the point lies in `N_v K_v` and the factor is `1` as before, and for
  non-integral `y_v` the spherical Whittaker function vanishes (by the Iwasawa decomposition
  the point has a non-dominant torus part, where `W_v` is zero by Shintani's formula). This
  is why the kernel carries the indicator of `rectIntegralOutside`.
* Nonvanishing: Jacquet 2009 (`jacquet-2009-archimedean-rankin-selberg`), Theorems 2.3, 2.6
  and 2.7, pp.8–10, at the infinite places, and the local theory of Jacquet,
  Piatetski-Shapiro and Shalika at the places of `S`. The dual integrals are not identically
  zero by the local functional equations. A choice of local data satisfying all of these
  conditions at once exists because each fails only on a proper subspace of the local model.

The premise packages results the Library does not contain: the tensor product decomposition
of a cuspidal representation with the factorization of its Whittaker functions at several
infinite places, the unramified computation of the dual kernel, and the nonvanishing theorems.
It is not formalized here.

## 4. The statement

`UnequalArchimedeanFactorizationReductionStatement.{u, uQ}` is the implication

```text
UnequalPointwiseFactorizationStatement.{u, uQ} → UnipotentClassProductStatement.{u} →
RectangleTateStatement.{u} → UnequalArchimedeanFactorizationStatement.{u, uQ}
```

with both universe parameters free, as in the target.

## 5. The proof of the reduction

`unequalArchimedeanFactorizationReduction` introduces A_U, B, C and all binders of (U), and
applies A_U to the same binders. This gives `x`, `x'` (spherical outside `S`), `κ`, `WR`,
`WR'`, `DR`, `WC`, `WC'`, `DC`, `D`, `fS`, `gS` and clauses 1–6. It applies B to `F`, `t`, `S`,
`DR`, `DC` and the quotient measures `(D v).quotientMeasure`, compatible by
`isCompatible_quotientMeasure`; this gives `C ≠ 0` and the product formula `hprod`. The
witnesses of (U) are `x`, `x'`, the constant `c = C · κ` (nonzero by `mul_ne_zero`), `WR`,
`WR'`, `DR`, `WC`, `WC'`, `DC`, `σ = 0` and `D`. The `Is…PlaceWhittaker` clauses and the four
nonvanishing clauses are those of A_U. The two identities are proved for every `s`; the
hypothesis `σ < Re s` is not used.

1. **The integral.** `partialUnequalWhittakerIntegral_eq_setIntegral` rewrites the partial
   integral as the integral over `unipotentIntegralClasses F m S`, which is measurable
   (`measurableSet_unipotentIntegralClasses`). `setIntegral_congr_fun` replaces the integrand
   by the right side of clause 4 on this set, `integral_const_mul` pulls out `κ`, and `hprod`
   (for `fR v = realUnequalIntegrand …`, `fC w = complexUnequalIntegrand …`, `fS v = fS v s`)
   gives `C` times the product of the local integrals. Clause 3 turns the local integrals at
   `S` into `(D v).integral h (νv v) s`. Unfolding `realUnequalIntegral`,
   `complexUnequalIntegral` and `unequalIntegral` shows that the archimedean integrals are
   `realUnequalIntegral h (DR v) …`, `complexUnequalIntegral h (DC w) …`, and `ring` gives
   `C κ · Ψ_∞(s) · ∏_(v ∈ S) (D v).integral h (νv v) s`.
2. **The dual integral.** For `q` in the set, the inner integral
   `dualWhittakerIntegrand F h Wdual W'dual s q = ∫ dualWhittakerKernel … q y d(rectangleMeasure)`
   is computed first (`key`): clause 5 rewrites the kernel for every `y`
   (`integral_congr_ae` with an everywhere statement), `integral_const_mul` pulls out `κ`, and
   C, applied to the functions `y ↦ realUnequalDualKernel h (WR v) (WR' v) s (q_v, y)`, its
   complex analogue and `y ↦ gS v s (q_v, y)`, gives `κ` times the product of the local
   rectangular integrals. Then, as in step 1, the partial dual integral becomes the integral of
   `key` over the set, `hprod` (for the functions `p ↦ ∫ (local dual kernel)(p, y) dy`) gives
   `C κ` times the product of iterated local integrals, and clause 3 turns those at `S` into
   `(D v).dualIntegral h (νv v) s`. Unfolding `realUnequalDualIntegral`,
   `complexUnequalDualIntegral`, `blockIntegral` and the dual kernels identifies the archimedean
   factors with `realUnequalDualIntegral h (aR v) (DR v) …` and
   `complexUnequalDualIntegral h (aC w) (DC w) …`, and `ring` concludes with the same constant
   `C κ`.

No integrability is used anywhere: all rewritings are pointwise identities of integrands on
the domain of integration, and the products of integrals come from B and C. `lean_check`
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## 6. The retained premises

All three premises are new here and open:

* `UnequalPointwiseFactorizationStatement.{u, uQ}` (A_U): representation theory (pure tensors,
  unramified computation, Jacquet 2009 and JPSS nonvanishing);
* `UnipotentClassProductStatement.{u}` (B): measure theory on `N(𝔸) \ GL(𝔸)`;
* `RectangleTateStatement.{u}` (C): Tate's normalization of the adelic additive measure.

Proving (U) unconditionally requires proofs of all three. The equal-rank conjunct of the task's
target is separate work.

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed p.219 (PDF p.222); the
  factorization of Whittaker functions of factorizable cusp forms, printed p.206 (PDF p.209).
* J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (1967),
  `tate-1967-thesis`, §2.2, printed p.310; Theorems 4.1.1–4.1.3, printed pp.328–331
  (PDF pp.173–174).
* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg`, Theorems 2.3, 2.6, 2.7, pp.8–10 (only in the
  justification of A_U).
