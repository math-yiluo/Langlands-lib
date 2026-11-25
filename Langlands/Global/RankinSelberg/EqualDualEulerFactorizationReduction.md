# Reduction of the equal-rank dual Euler factorization to the direct one

Module `Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction`.

## 1. Content and provenance

The published statement
`Langlands.Global.RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ}`
([`EqualDualEulerFactorizationStatement`](EqualDualEulerFactorizationStatement.md), called
(D) here) is the partial Euler factorization of the dual global Whittaker integral
`Ψ(s; W̃, W̃', Φ̂)` of two actual cuspidal realizations `T`, `T'` of `GL_n`, `n = r + 1`,
expressed through spectral presentations `Pd`, `Pd'` of contragredient realizations `Td`,
`Td'`. Its companion
[`EqualEulerFactorizationStatement`](EqualEulerFactorizationStatement.md) (called (E) here)
is the same factorization for `Ψ(s; W, W', Φ)` and presentations of `T`, `T'`. This module
contains, in the namespace `Langlands.Global.RankinSelbergGlobal`:

* two new Prop-valued premises, `ContragredientDualWhittakerStatement` and
  `FourierStandardOutsideStatement` (Section 2);
* the statement `EqualDualEulerFactorizationReductionStatement.{u, uQ}` (Section 3): (E),
  the published `SchwartzBruhatStatement` and the two new premises together imply (D);
* the theorem `equalDualEulerFactorizationReduction`, which proves it (Section 5);
* the inverse `inverseCharacter ψ` of a unitary additive character and five lemmas about it
  (Section 4).

The theorem is a reduction. It does not prove (D); the state of its four premises is given
in Section 6. The Library proves (D) as `equalDualEulerFactorization` (module
`EqualDualEulerFactorizationProof`).

**Source of the reduction.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in
Bernstein–Gelbart (eds.), *An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3). On p.211 (Theorem 2.2 and
the remark after it) the dual side `I(1 − s; φ̃, φ̃', Φ̂)` of the equal-rank functional
equation unfolds to `Ψ(1 − s; W̃_φ, W̃'_φ', Φ̂)` and factors "as before", that is, by the
argument of p.210 for `Ψ(s; W_φ, W'_φ', Φ)`. Here `φ̃(g) = φ(w_n ᵗg⁻¹)` (p.206) is a cusp
form in the contragredient `π̃`, and its `ψ⁻¹`-Whittaker function is
`W̃_φ(g) = W_φ(w_n ᵗg⁻¹)` (pp.201 and 207). So the dual integral is the direct integral of
the pair `(π̃, π̃')` for the character `ψ⁻¹`, evaluated at the cusp forms `φ̃`, `φ̃'` and at
the Schwartz–Bruhat function `Φ̂`. This module makes that observation formal: it applies (E)
to `ψ⁻¹`, `Td`, `Td'`, `Pd`, `Pd'` and `Φ̂`.

**Provenance (internal).** The decomposition into premises is ours. (E) and
`SchwartzBruhatStatement` are published Library statements. The two new premises isolate
the two facts the observation above needs: that `W̃_x` is
the Whittaker function of a vector of `Td` (Cogdell pp.201–202, 206–207), and that `Φ̂`
inherits the condition `IsStandardOutside` from `Φ` (Tate's local computation, used by
Cogdell p.211 when he factors `Φ̂ = ⊗ Φ̂_v`).

## 2. The new premises

### 2.1 `ContragredientDualWhittakerStatement`

For every number field `F : Type u` with `CompactSpace (AdeleQuotient F)`, every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` trivial on `F`, every `r`, every
pair `T`, `Td` of actual cuspidal realizations of `GL_(r+1)` with
`Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization`, every
finite set `S` of finite places and every `x : T.Space` with `IsSphericalOutside F T S x`,
there is `xd : Td.Space` with `IsSphericalOutside F Td S xd` and

```text
cuspWhittaker F Td ψ.complex⁻¹ xd = dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x).
```

Here `cuspWhittaker F T ψ x` is the global Whittaker function
`W_x(g) = ∫_(N(F)\N(𝔸)) φ_x(n g) conj(ψ_N(n)) dn` of the cusp form `φ_x` of `x` (total mass
one), and `dualFunction F n W` is `g ↦ W(w_n ᵗg⁻¹)`. `IsSphericalOutside` means fixed by
`GL_(r+1)(𝒪_v)` at every finite place `v ∉ S`.

**Sources.** Cogdell 2004:

* p.201 (PDF p.204), after Theorem 1.2: by Gelfand–Kazhdan `π̃_v ≅ π_v^ι` for
  `g^ι = ᵗg⁻¹`, and the Whittaker model of `π̃_v` is
  `W(π̃_v, ψ_v⁻¹) = {W̃(g) = W(w_n ᵗg⁻¹) | W ∈ W(π_v, ψ_v)}`.
* p.202 (PDF p.205): a cusp form is determined by its Whittaker function, and the Multiplicity
  One Theorem: an irreducible representation occurs at most once in the cusp forms.
* p.206 (PDF p.209): `φ̃(g) = φ(g^ι) = φ(w_n g^ι)`; the dual integral uses `φ̃ ∈ V_π̃`.
* p.207 (PDF p.210): "for `W ∈ W(π, ψ)`, we set `W̃(g) = W(w_n g^ι) ∈ W(π̃, ψ⁻¹)`", and
  `W̃_φ = W_φ̃` for the cusp form `φ̃`.

**Why it holds.** Let `φ` be the cusp form of `x`. The functions `φ̃`, `φ ∈ V_π`, form a
cuspidal representation isomorphic to `π^ι ≅ π̃` (Gelfand–Kazhdan). By multiplicity one this
space is the space of cusp forms of `Td`, so `φ̃` is the cusp form of some `xd : Td.Space`.
The substitution `n ↦ w_n ᵗn⁻¹ w_n⁻¹` preserves `N(F)\N(𝔸)` and its measure and turns
`ψ_N` into `ψ_N⁻¹`, which gives `W^(ψ⁻¹)_(φ̃)(g) = W^ψ_φ(w_n ᵗg⁻¹)`. Finally `ᵗk⁻¹ ∈ GL_n(𝒪_v)`
for `k ∈ GL_n(𝒪_v)`, so `φ̃` is right `GL_n(𝒪_v)`-invariant when `φ` is. The premise records
the conclusion of this argument at the level of Whittaker functions. The Library has no
multiplicity one theorem and no Gelfand–Kazhdan theorem, and its contragredient realizations
are defined by invariant pairings (module `Langlands.Automorphic.Contragredient`), not by
`φ ↦ φ̃`.

### 2.2 `FourierStandardOutsideStatement`

For every number field `F : Type u`, every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` and every finite set `S` of finite
places with `FunctionalEquationComparison.FiniteAdditiveSupport ψ S`, and for every `n` and
every `Φ : RowVector F n → ℂ`,

```text
IsStandardOutside F n S Φ → IsStandardOutside F n S (fourierTransform F n ψ.complex Φ).
```

`FiniteAdditiveSupport ψ S` says that at every finite `v ∉ S` the canonical component `ψ_v`
of `ψ` has conductor `0`, that is, it is trivial on `𝒪_v` and not on `ϖ_v⁻¹ 𝒪_v`.
`IsStandardOutside F n S Φ` says that `Φ(x) = 0` unless `x_v ∈ 𝒪_v^n` for every finite
`v ∉ S`, and that on that set `Φ(x)` depends only on the coordinates of `x` at the infinite
places and at the places of `S`. For a pure tensor this is `Φ_v = 1_(𝒪_v^n)` at every finite
`v ∉ S`. `fourierTransform F n ψ Φ (x) = ∫ Φ(y) ψ(∑_j y_j x_j) d(rectangleMeasure F 1 n)(y)`.

**Sources.** J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*
(1950 thesis, in Cassels–Fröhlich 1967), registered as `tate-1967-thesis`, §2.2, printed
pp.309–311 (PDF pp.163–164): Lemma 2.2.3 (p.309), the character attached to `η` is trivial
on `𝒪` exactly when `η ∈ 𝔡⁻¹`; p.310, the self-dual measure gives `𝒪` volume `(N𝔡)^(−1/2)`
and Theorem 2.2.2 is Fourier inversion for it; p.311, `1_𝒪` is the test function in the
`p`-adic case. When the conductor of `ψ_v` is `𝒪_v` this gives
`(1_(𝒪_v^n))^ = 1_(𝒪_v^n)`, which Cogdell uses on p.211 for `Φ̂ = ⊗_v Φ̂_v`. The Markdown of
(D) gives the same argument (section "`Φ̂` is standard outside `S`").

**Why it holds for every `Φ`.** The premise needs no integrability, and its conclusion does
not depend on the normalization of the Haar measure. If `x_v ∉ 𝒪_v^n` for some finite
`v ∉ S`, pick `a ∈ 𝒪_v` in the coordinate where `x_v` is not integral with
`ψ_v(a x_(v,j)) ≠ 1`. `Φ` is invariant under translation by the adele `e` that is `a` in that
coordinate at `v` and `0` elsewhere, so translation invariance of the measure gives
`Φ̂(x) = ψ(e·x) Φ̂(x)`, hence `Φ̂(x) = 0`. If `x`, `x'` are integral outside `S` and agree at
the infinite places and at `S`, then for every `y` with `Φ(y) ≠ 0` the adele
`y·(x' − x)` is `0` at the infinite places and at `S` and integral elsewhere. Every
`ψ_v`, `v ∉ S`, is trivial on `𝒪_v`, and `ψ` is continuous, so `ψ(y·(x' − x)) = 1` and
`Φ̂(x) = Φ̂(x')`. This argument is not formalized here.

## 3. The statement

`EqualDualEulerFactorizationReductionStatement.{u, uQ}` is the implication

```text
EqualEulerFactorizationStatement.{u, uQ} → SchwartzBruhatStatement.{u} →
ContragredientDualWhittakerStatement.{u} → FourierStandardOutsideStatement.{u} →
EqualDualEulerFactorizationStatement.{u, uQ}
```

* (E), `EqualEulerFactorizationStatement`: for `ψ`, `T`, `T'`, presentations `P`, `P'` and
  `S` as in (D), there is `σ` such that for `x`, `x'` spherical outside `S`, `Φ` Schwartz–Bruhat
  and standard outside `S`, `W = cuspWhittaker F T ψ.complex x`,
  `W' = cuspWhittaker F T' ψ.complex⁻¹ x'` and `σ < Re s`, the integrand of `Ψ(s; W, W', Φ)` is
  integrable, the Euler product of `partialEulerFactor P P'` converges absolutely, and
  `Ψ(s; W, W', Φ) = Ψ_(S∪∞)(s; W, W', Φ) · ∏_(v ∉ S) L_v(s)`.
* `SchwartzBruhatStatement` (Getz–Hahn §C.3): the Schwartz–Bruhat space is the restricted
  tensor product space, and for a standard additive character (`IsStandardAdditiveCharacter`)
  the Fourier transform of a Schwartz–Bruhat function is integrable, Schwartz–Bruhat, and
  satisfies Fourier inversion.
* The two premises of Section 2.

The module declares the same two local instances as (D) and (E): the Library theorems
`GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement` made available to instance search. They add no
hypothesis.

## 4. The inverse character and auxiliary lemmas

* `inverseCharacter ψ`, for a `UnitaryAdditiveCharacter` `ψ` of a topological additive group
  `A`, is the character `a ↦ ψ(a)⁻¹`, built from `ψ.toAddChar⁻¹`. Continuity is that of
  inversion on the circle, and nontriviality follows from that of `ψ`.
* `inverseCharacter_apply`: `inverseCharacter ψ a = (ψ a)⁻¹`.
* `complex_inverseCharacter`: `(inverseCharacter ψ).complex = ψ.complex⁻¹` in
  `AddChar A ℂ`. Both sides send `a` to the complex value of `ψ(−a)`.
* `inverseCharacter_rational`: if `ψ` is trivial on `F`, so is `inverseCharacter ψ`.
* `additiveConductor_inverseCharacter`: for a `p`-adic field `K` with topological data `T`,
  `T.additiveConductor (inverseCharacter ψ) = T.additiveConductor ψ`. The two characters are
  trivial on the same balls, and `additiveTrivialAt_iff_le_conductor` with
  `additiveConductor_spec` compares the conductors in both directions.
* `finiteAdditiveSupport_inverseCharacter`: `FiniteAdditiveSupport ψ S` implies
  `FiniteAdditiveSupport (inverseCharacter ψ) S`. At `v ∉ S` the witness is
  `inverseCharacter ψ_v`. It is the canonical component of `inverseCharacter ψ`, because
  both sides of the defining identity are inverted, and its conductor is `0` by the previous
  lemma.
* `isStandardAdditiveCharacter_of_unitary`: if `ψ` is trivial on `F` then
  `IsStandardAdditiveCharacter F ψ.complex`. Continuity and `‖ψ.complex a‖ = 1` come from
  the API of `UnitaryAdditiveCharacter`, and `ψ.complex ≠ 1` from `ψ.nontrivial`.

## 5. The proof of the reduction

`equalDualEulerFactorizationReduction` introduces the four premises and the binders of (D):
`F`, `ψ`, `hψ`, `r`, `T`, `Td`, `T'`, `Td'`, the contragredience hypotheses `hTd`, `hTd'`,
`Pd`, `Pd'`, `S`, `hPd`, `hPd'` and `hS : FiniteAdditiveSupport ψ S`.

1. Apply (E) to `F`, `ψ⁻¹ = inverseCharacter ψ` (trivial on `F` by
   `inverseCharacter_rational`), the realizations `Td`, `Td'`, their presentations `Pd`, `Pd'`,
   `S`, `hPd`, `hPd'` and `FiniteAdditiveSupport ψ⁻¹ S`
   (`finiteAdditiveSupport_inverseCharacter`). This gives `σ` and the property `hσ`, and `σ`
   is the witness of (D).
2. Given `x`, `x'`, `Φ` with their hypotheses, apply `ContragredientDualWhittakerStatement`
   to `ψ`, `T`, `Td`, `x`. This gives `xd : Td.Space`, spherical outside `S`, with
   `cuspWhittaker F Td ψ.complex⁻¹ xd = Wdual`.
3. Apply it to `ψ⁻¹`, `T'`, `Td'`, `x'`. This gives `xd' : Td'.Space`, spherical outside `S`,
   with `cuspWhittaker F Td' (ψ⁻¹).complex⁻¹ xd' = dualFunction (cuspWhittaker F T' (ψ⁻¹).complex x')`.
   Rewriting with `complex_inverseCharacter` and `inv_inv` turns this into
   `cuspWhittaker F Td' ψ.complex xd' = W'dual`.
4. `Φhat ∈ schwartzBruhat F (r + 1)` by the second part of `SchwartzBruhatStatement` for
   `ψ.complex`, which is standard by `isStandardAdditiveCharacter_of_unitary`.
   `IsStandardOutside F (r + 1) S Φhat` by `FourierStandardOutsideStatement`.
5. Apply `hσ` to `xd`, `xd'` and `Φhat`. Its Whittaker functions are
   `cuspWhittaker F Td (ψ⁻¹).complex xd` and `cuspWhittaker F Td' (ψ⁻¹).complex⁻¹ xd'`.
   Rewriting with `complex_inverseCharacter`, `inv_inv` and the identities of steps 2 and 3
   turns them into `Wdual` and `W'dual`. The Euler factors are `partialEulerFactor Pd Pd'`
   on both sides, so the result is exactly the conclusion of (D) for every `s` with
   `σ < Re s`.

The proof uses no other hypothesis. `lean_check` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## 6. The retained premises

The four premises in the Library:

* `EqualEulerFactorizationStatement.{u, uQ}`: published; proved by `equalEulerFactorization`
  (module `EqualEulerFactorizationProof`).
* `SchwartzBruhatStatement.{u}`: published; proved by
  `SchwartzBruhatProof.schwartzBruhatStatement_proof` (module `SchwartzBruhatProof`).
* `FourierStandardOutsideStatement.{u}`: new here; proved by `fourierStandardOutside` (module
  `FourierStandardOutsideProof`).
* `ContragredientDualWhittakerStatement.{u}`: new here; `contragredientDualWhittakerReduction`
  (module `ContragredientDualWhittakerReduction`) reduces it to two premises that the Library
  proves, but no theorem states it unconditionally.

An unconditional proof of (D) through this reduction needs proofs of all four.
