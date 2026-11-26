# Factorization of the partial Whittaker integrals over `S` and the infinite places

Module `Langlands.Global.RankinSelberg.ArchimedeanFactorizationStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. It states result 2 of `ArchimedeanSemilocalTheoryStatement`, Cogdell 2004, proof of
Theorem 4.1, p.219 (unequal ranks) and p.220 (equal ranks, "entirely analogous"), in both rank
cases:

* `UnequalArchimedeanFactorizationStatement` (`t < r`);
* `EqualArchimedeanFactorizationStatement` (equal ranks, including `r = 0`);
* `ArchimedeanFactorizationStatement`, their conjunction.

It also defines two coordinate maps used in the equal-rank statement:

* `realRowCoordinates F n v x : Fin n → ℝ`, the coordinates `x_v` of an adelic row vector
  `x ∈ 𝔸^n` at the real place `v`;
* `complexRowCoordinates F n w x : Fin n → ℂ`, the coordinates `x_w` at the complex place `w`.

Both read off the `v`- (or `w`-) component of the Library's mixed archimedean coordinates
`archimedeanCoordinates F n x` (Mathlib's `InfiniteAdeleRing.ringEquiv_mixedSpace`). That ring
isomorphism is built from `InfinitePlace.Completion.ringEquivRealOfIsReal` and
`ringEquivComplexOfIsComplex`, the identifications through which `IsRealAdditiveComponent` and
`IsComplexAdditiveComponent` describe the archimedean components of `ψ`. So in these
coordinates the restriction of `ψ` to the place is `realScaledCharacter (aR v)` or
`complexScaledCharacter (aC w)`. At a finite place `v` the Library's `localCoordinates F n v x`
lies in `FiniteCompletion F v = v.adicCompletion F`, which is by definition the carrier of
`padicField v`, so the local test functions of `EqualLocalTestData` apply to it directly.

`EqualArchimedeanFactorizationAt F` is the integrated equal-rank proposition with the field
`F` specified. Its universal closure is `EqualArchimedeanFactorizationStatement`. The
number-field universe `u` and the presentation universe `uQ` are independent.

## `UnequalArchimedeanFactorizationStatement`

**Hypotheses.** Exactly the binders of `UnequalSemilocalFactorizationStatement`, in the same
order: `F`, `ψ` trivial on `F`, `t < r`, `T`, `Td`, `T'`, `Td'` with the contragredient
hypotheses, spectral presentations `P`, `P'` with irreducible admissible components, a finite
set `S` of finite places containing `P.exceptional` and `P'.exceptional` with
`FiniteAdditiveSupport ψ S`, the archimedean components `aR`, `aC` of `ψ`, the parameters
`dR`, `dR'`, `dRd`, `dRd'`, `dC`, `dC'`, `dCd`, `dCd'` with their hypotheses, canonical finite
components `ψv` of `ψ` and measures `νv` self-dual for them. The `let`s `infiniteL`,
`dualInfiniteL`, `infiniteEpsilon` of the target are omitted, since they are not used.

**Conclusion.** There exist

* `x ∈ T.Space` and `x' ∈ T'.Space`, spherical outside `S` (`IsSphericalOutside`);

such that, with `W = cuspWhittaker F T ψ x`, `W' = cuspWhittaker F T' ψ⁻¹ x'`,
`Wdual = ρ(w_(n,m)) W̃` and `W'dual = W̃'` defined exactly as in the target
(`translateFunction`, `unfoldingWeyl`, `dualFunction`), there exist

* `c ∈ ℂ`;
* for each real place `v`, functions `WR v` on `GL_(r+1)(ℝ)` and `WR' v` on `GL_(t+1)(ℝ)`,
  and quotient measure data `DR v : RealQuotientMeasureData t`;
* for each complex place `w`, functions `WC w`, `WC' w` and data
  `DC w : ComplexQuotientMeasureData t`;
* `σ ∈ ℝ`;
* for each `v ∈ S`, test data `D v : PadicUnequalTestData` for the actual local components
  `((P.localComponent v).padicObject …).obj.representation` and the same for `P'`, and the
  character `ψv v`: a compatible quotient measure, nonzero Whittaker functionals for `ψv v`
  and its inverse, and one vector of each coefficient model;

with:

1. `c ≠ 0`;
2. `IsRealPlaceWhittaker F T ψ v (WR v)` and `IsRealPlaceWhittaker F T' ψ⁻¹ v (WR' v)` for
   every real `v`, and `IsComplexPlaceWhittaker` likewise for `WC w`, `WC' w`. These are the
   hypotheses of result 1 (`ArchimedeanFunctionalEquationStatement`) for these data;
3. for `σ < Re s`,
   `partialUnequalWhittakerIntegral F h S W W' s = c · Ψ_∞(s) · ∏_(v ∈ S) (D v).integral h (νv v) s`,
   where `Ψ_∞(s) = ∏_(v real) Ψ(s; WR v, WR' v) · ∏_(w complex) Ψ(s; WC w, WC' w)` with the
   integrals of `ArchimedeanIntegrals` for `DR v`, `DC w`;
4. for `σ < Re s`,
   `partialDualWhittakerIntegral F h S Wdual W'dual s = c · Ψ̃_∞(s) · ∏_(v ∈ S) (D v).dualIntegral h (νv v) s`,
   with the same `c`, where `Ψ̃_∞(s)` is the product of the dual block integrals
   `Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃_v, W̃'_v)`, the inner variable taken with the measure self-dual
   for `aR v`, `aC w`;
5. none of `Ψ_∞`, `Ψ̃_∞`, `(D v).integral h (νv v)` and `(D v).dualIntegral h (νv v)`
   (`v ∈ S`) vanishes identically on a right half-plane: for every `a ∈ ℝ` there is `s` with
   `a < Re s` at which it is nonzero.

The local integrals at `v ∈ S` are those recorded by `PadicUnequalTestData.integral` (block
`0`) and `PadicUnequalTestData.dualIntegral` (block `r − t − 1`, with `νv v` on the inner
variable), as in the target.

## `EqualArchimedeanFactorizationStatement`

**Hypotheses.** Exactly the binders of `EqualSemilocalFactorizationStatement` (without its
`let`s for `L_∞`, `L∨_∞`, `ε_∞`).

**Conclusion.** There exist `x`, `x'` spherical outside `S` and
`Φ ∈ schwartzBruhat F (r + 1)` with `IsStandardOutside F (r + 1) S Φ`, such that, with `W`,
`W'`, `Wdual = W̃`, `W'dual = W̃'` and `Φhat = fourierTransform F (r + 1) ψ Φ` defined exactly as
in the target, there exist `c`, archimedean functions `WR v`, `WR' v`, `WC w`, `WC' w`,
Schwartz functions `ΦR v : SchwartzMap (Fin (r+1) → ℝ) ℂ` and
`ΦC w : SchwartzMap (Fin (r+1) → ℂ) ℂ`, quotient measure data `DR v`, `DC w`, `σ`, and
`D v : EqualLocalTestData (padicField v) (ψv v) (νv v) π_v π'_v` for `v ∈ S`, with:

1. `c ≠ 0`;
2. the `Is…PlaceWhittaker` conditions as above;
3. the pointwise factorization of the test function: for every row vector `y`,
   `Φ(y) = 1_(integralOutside F (r+1) S)(y) · ∏_(v real) ΦR v (y_v) · ∏_(w complex) ΦC w (y_w) · ∏_(v ∈ S) (D v).Φ (y_v)`,
   that is, `Φ = Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^(r+1))` with `Φ_∞ = ⊗_v ΦR v ⊗ ⊗_w ΦC w`
   (the shape of `IsRestrictedPureSchwartzBruhat`); here `y_v` is `realRowCoordinates`,
   `complexRowCoordinates` or `localCoordinates`;
4. the pointwise factorization of its Fourier transform, with constant exactly one:
   `Φhat(y) = 1_(integralOutside F (r+1) S)(y) · ∏_(v real) Φ̂R_v (y_v) · ∏_(w complex) Φ̂C_w (y_w) · ∏_(v ∈ S) (D v).Φhat (y_v)`,
   where `Φ̂R_v = realFourierTransform (aR v) (ΦR v)` and
   `Φ̂C_w = complexFourierTransform (aC w) (ΦC w)` are the archimedean transforms of result 1
   (for the components of `ψ` and their self-dual measures), and `(D v).Φhat` is the Fourier
   partner of `(D v).Φ` for `ψv v` and `νv v` recorded in `D v` (`IsRowFourierPair`). So
   `Φ̂ = Φ̂_∞ ⊗ ⊗_(v ∈ S) Φ̂_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^(r+1))`. Because the local functions in
   clauses 3 and 4 are the ones entering the integrals of clauses 5 and 6, a rescaling of
   one local factor must be compensated by another local factor, not by `c`;
5. for `σ < Re s`,
   `partialEqualWhittakerIntegral F S W W' Φ s = c · Ψ_∞(s) · ∏_(v ∈ S) (D v).integral s`, with
   `Ψ_∞(s) = ∏_(v real) Ψ(s; WR v, WR' v, ΦR v) · ∏_(w complex) Ψ(s; WC w, WC' w, ΦC w)`;
6. for `σ < Re s`,
   `partialEqualWhittakerIntegral F S Wdual W'dual Φhat s = c · Ψ̃_∞(s) · ∏_(v ∈ S) (D v).dualIntegral s`,
   with the same `c`, where `Ψ̃_∞(s)` is the product of `Ψ(s; W̃_v, W̃'_v, Φ̂_v)`, `Φ̂_v` being the
   Fourier transform of `ΦR v` or `ΦC w` for `aR v` or `aC w` and the self-dual measure;
7. none of `Ψ_∞`, `Ψ̃_∞`, `(D v).integral`, `(D v).dualIntegral` vanishes identically on a
   right half-plane.

Mathematically, clause 3 already implies `Φ ∈ schwartzBruhat F (r + 1)` (a product of Schwartz
functions of the separate archimedean coordinates is a Schwartz function of the mixed
coordinates, and the finite part is locally constant with compact support) and
`IsStandardOutside F (r + 1) S Φ`. This is not proved here, and both conditions are kept
because the target states them.

`EqualLocalTestData` contains the local Fourier pair `(Φ_v, Φ̂_v)` for `ψv v` and `νv v`
(`IsRowFourierPair`), and its dual integral uses `Φ̂_v`.

## Why it holds (Cogdell, pp.219–220)

The statement is not proved here. The expected proof is Cogdell's.

* **Pure tensors.** Take `x`, `x'` pure tensors: `W_x(g) = ∏_v W_v(g_v)` over all places, with
  `W_v` the normalized spherical Whittaker function (`W_v(1) = 1`) for `v ∉ S ∪ ∞`. The local
  components at `v ∉ S` are unramified because `S ⊇ P.exceptional`.
* **Archimedean restrictions.** Choose the archimedean `W_u` with `W_u(1) ≠ 0` as well as
  with a nonvanishing integral. This is possible: each condition fails only on a proper
  subspace of the local model, and a complex vector space is not the union of two proper
  subspaces. Take a finite adelic point `a` with `W_u(a_u) ≠ 0` at every finite `u`. The
  restriction `g ↦ W_x(ι_v(g) a)` at an infinite place `v` is then `λ_v W_v`, with
  `λ_v = ∏_(u ≠ v) W_u(a_u)` (`a_u = 1` at the other infinite places), a nonzero constant.
  The local dual of the restriction is `λ_v W̃_v`, with the same `λ_v`. So `WR v`, `WC w` are
  restrictions in the sense of `IsRealPlaceWhittaker`, `IsComplexPlaceWhittaker`, and the
  constants `λ_v` are absorbed in `c`. Taking the archimedean factor as the global integral
  restricted to finite part `1` would not work: the global `W̃` brings the finite values
  `W_u(w_n …)` into it.
* **Places outside `S ∪ ∞`.** They do not appear in the partial integrals; they contribute
  only through the values `W_u(1)` and `W̃_u(1) = W_u(w_n) = W_u(1)` (`w_n ∈ GL_n(𝒪_u)`), which
  agree. In unequal ranks the inner variable of the dual integral at such `u` contributes `1`:
  the unramified `W_u` is supported on integral `X` (Shintani), and the self-dual measure for
  the unramified `ψ_u` gives `M(𝒪_u)` volume `1`.
* **Measures.** `rectangleMeasure` has covolume one, as has the product of the local measures
  self-dual for `ψ_v` (`νv v` at finite places, `|a|^(1/2) dx` or `|a| · 2 dx dy` at the infinite
  places, volume one on `M(𝒪_u)` outside `S`), because `ψ` is trivial on `F`. The comparison of
  `whittakerQuotientMeasure` with the product of the local quotient measures (`DR v`, `DC w`
  and the measure of `D v`) is one constant, the same for an integral and its dual; it is
  absorbed in `c`.
* **Equal ranks: the test function (clauses 3 and 4).** Take
  `Φ = Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` with `Φ_∞ = ∏_v ΦR v ⊗ ∏_w ΦC w`, `Φ_v` any
  Schwartz–Bruhat function at `v ∈ S`, and `(D v).Φhat` its transform (which is again
  Schwartz–Bruhat). Clause 3 then holds by construction. The global Fourier transform
  (positive sign, `rectangleMeasure F 1 n` of covolume one) is
  `Φ̂ = Φ̂_∞ ⊗ ⊗_(v ∈ S) Φ̂_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` with constant exactly one, which is clause 4.
  The reasons: the local transforms are for the self-dual measures, and their product is a
  Haar measure on `𝔸^n` of covolume one (Tate), hence equal to `rectangleMeasure F 1 n`; in the
  coordinates above, `ψ(∑_j y_j x_j)` is the product of the local characters
  `realScaledCharacter (aR v)`, `complexScaledCharacter (aC w)` and `ψv v` evaluated at
  `∑_j y_(v,j) x_(v,j)`; and `1_(𝒪_v^n)` is its own transform for unramified `ψ_v`
  (`FiniteAdditiveSupport ψ S`) with the self-dual measure, which gives `𝒪_v` volume one. So
  no constant enters `Φ̂`, and the constant of the dual integral is the `c` of the integral.
* **Nonvanishing.** At each place one can choose the local data with an integral that is not
  identically zero (Jacquet 2009, Theorems 2.3, 2.6, 2.7, pp.8–10, at the infinite places; the
  local theory of Jacquet–Piatetski-Shapiro–Shalika at the finite places). The dual integrals
  are then not identically zero by the local functional equations.

## Normalizations

As in result 1 (Markdown of `ArchimedeanFunctionalEquationStatement`): normalized absolute
values, self-dual measures for `aR v`, `aC w`, positive Fourier sign, `w_n = weylLong`,
`ρ(w_(n,m))` by `unfoldingWeyl`. At the finite places the conventions are those of
`PadicUnequalTestData` and `EqualLocalTestData`.

## Choices of form

* **Same constant.** One `c` for the integral and its dual. A constant that differed between
  them would enter the sign clause of the targets, where it cannot be absorbed (the equal-rank
  target forces its `κ` through the sign clause).
* **Existential data.** All data are existential: the consumers need one good choice.
* **Archimedean data at every infinite place.** The data are indexed by the real and the
  complex places. Result 2 does not assume result 1. Over a totally complex field the real
  index type is empty, and the real factors are empty products.
* **Nonvanishing of the dual integrals** is included, so that the consumers' continuations of
  `Ψ̃_∞` are not identically zero without a further argument.

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3): proof of Theorem 4.1,
  p.219 (factorization for "appropriate" `φ`, `φ'`, unequal ranks) and p.220 (equal ranks).
* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg`, pp.8–10: Theorems 2.3, 2.6 and 2.7 (nonvanishing
  of suitable archimedean integrals).

## Provenance

Source statement: Cogdell 2004, proof of Theorem 4.1, pp.219–220, with "appropriate" data
made precise as the existence of the data above, and with the infinite places kept separate
from the finite set `S`, as in the targets.
