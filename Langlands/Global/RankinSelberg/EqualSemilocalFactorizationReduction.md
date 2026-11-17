# Reduction of the equal-rank factorization premise to the archimedean theory

Module `Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReduction`. Author: Worker 5014.

## 1. Content and status

The published proposition
`Langlands.Global.RankinSelbergGlobal.EqualSemilocalFactorizationStatement.{u, uQ}` (module
[`EqualSemilocalReduction`](EqualSemilocalReduction.md), Section 3 of its Markdown; called (P)
here) is the premise of the conditional reduction `equalSemilocalReduction` of the equal-rank
semi-local functional equation. This module contains, in the namespace
`Langlands.Global.RankinSelbergGlobal`:

* the Prop-valued statement `EqualSemilocalFactorizationReductionStatement.{u, uQ}`
  (Section 2), the implication from four published statements of the archimedean theory to
  (P);
* the theorem `equalSemilocalFactorizationReduction :
  EqualSemilocalFactorizationReductionStatement.{u, uQ}`, which proves it (Section 4);
* the theorem `equalSemilocalFactorization_of_archimedeanSemilocalTheory`, which derives (P)
  from the conjunction `ArchimedeanSemilocalTheoryStatement.{u, uQ}` (Section 4);
* two helper lemmas in the namespace `EqualSemilocalFactorizationReduction` (Section 3);
* two local instances (`IsAffine` and `Smooth` for the `GL_n` scheme) that the statements
  need in order to elaborate, as in the module `EqualSemilocalReduction`.

The theorem is a **conditional reduction**. It does not prove (P): its four premises are
open statements, stated in the Library by Task 7136 and proved nowhere in the Library. It is
an intermediate result of Task 7124 in the sense of the "Intermediate results" section of
that task's revision 1. The task's required result, an unconditional proof of (P), stays
open.

## 2. The statement

`EqualSemilocalFactorizationReductionStatement.{u, uQ}` is the implication

```
ComplexEqualFunctionalEquationStatement.{u} → RealEqualFunctionalEquationStatement.{u} →
  EqualArchimedeanFactorizationStatement.{u, uQ} → ArchimedeanCentralSignStatement.{u, uQ} →
    EqualSemilocalFactorizationStatement.{u, uQ}
```

with the four premises, all in the namespace `Langlands.Global.RankinSelbergGlobal`:

1. `ComplexEqualFunctionalEquationStatement` (module
   [`ArchimedeanFunctionalEquationStatement`](ArchimedeanFunctionalEquationStatement.md)):
   at a complex place, for equal ranks, the archimedean integral and its dual integral (for
   the Fourier transform of the Schwartz function) converge and are holomorphic on a right
   half-plane `σ < Re s`, agree there with functions `M`, `Md` meromorphic on `ℂ`, and satisfy
   the local functional equation off a discrete set, with the sign
   `complexMinusOneScalar T' w ^ r` (Jacquet 2009, Theorem 2.1).
2. `RealEqualFunctionalEquationStatement` (same module): the same at a real place, with the
   sign `realMinusOneScalar T' v ^ r`.
3. `EqualArchimedeanFactorizationStatement` (module
   [`ArchimedeanFactorizationStatement`](ArchimedeanFactorizationStatement.md)): with the
   binders of (P), there are `x`, `x'`, `Φ` and a constant `c ≠ 0`, archimedean data and
   local test data `D v` (`v ∈ S`) such that, for `σ₂ < Re s`, the partial integral is
   `c Ψ_∞(s) ∏_(v ∈ S) (D v).integral s` and the dual partial integral is
   `c Ψ̃_∞(s) ∏_(v ∈ S) (D v).dualIntegral s`, with none of `Ψ_∞`, `Ψ̃_∞`, `(D v).integral`,
   `(D v).dualIntegral` vanishing identically on a right half-plane (Cogdell 2004,
   pp.219–220).
4. `ArchimedeanCentralSignStatement` (module
   [`ArchimedeanCentralSignStatement`](ArchimedeanCentralSignStatement.md)): for scalars
   `ζ_v` (`v ∈ S`) by which `−1` acts on the models of nonzero Whittaker functionals for
   `ψv v⁻¹` on the local components of `P'`,
   `(∏_(v real) ω'_v(−1)) (∏_(w complex) ω'_w(−1)) ∏_(v ∈ S) ζ_v = 1` (Cogdell 2004, p.220).

The premises are the equal-rank components of the conjunction
`ArchimedeanSemilocalTheoryStatement = ArchimedeanFunctionalEquationStatement ∧
ArchimedeanFactorizationStatement ∧ ArchimedeanCentralSignStatement` (module
[`ArchimedeanSemilocalTheoryStatement`](ArchimedeanSemilocalTheoryStatement.md)):
`ComplexEqual…` is the second conjunct of `ComplexPlaceFunctionalEquationStatement`,
`RealEqual…` the second conjunct of `RealPlaceFunctionalEquationStatement`, and
`EqualArchimedeanFactorizationStatement` the second conjunct of
`ArchimedeanFactorizationStatement`. The unequal-rank components are not used.

**Provenance.** The statement is internal: an implication between published Library
statements, written for Task 7124. Its argument follows the sketch "Derivation of
`EqualSemilocalFactorizationStatement`" in the Markdown of `ArchimedeanSemilocalTheoryStatement`
(Task 7136), which in turn follows Cogdell 2004, proof of Theorem 4.1, pp.219–220 (the global
integral is a constant times the product of the archimedean and the local integrals at `S`,
and the archimedean functional equations multiply). The source citations of the four
premises are in their own Markdown.

## 3. Helper lemmas

In the namespace `Langlands.Global.RankinSelbergGlobal.EqualSemilocalFactorizationReduction`:

* `analyticAt_of_eq_on_halfPlane`: if `f` is complex-differentiable on the open half-plane
  `{σ < Re s}` and `f s = g s` there, then `g` is analytic at every point of the half-plane
  (`DifferentiableOn.congr`, `DifferentiableOn.analyticAt`).
* `mul_combine`: from `A B = X Y E N` and `A' B' = X' Y' E' N'` follows
  `A A' (c B B') = X X' (Y Y') (E E') (c N N')` (`linear_combination`). It multiplies the real
  and the complex functional equations and the constant `c`.

## 4. The proof of `equalSemilocalFactorizationReduction`

Introduce the four premises `hC`, `hR`, `h2`, `h3` and all binders of (P), including `ψv`, `νv`.

* **Step 1 (factorization).** Apply `h2` to the same binders. It gives `x`, `x'`, `Φ` and
  their four properties, which are the first witnesses of (P). After the `let`s `W`, `W'`,
  `Wdual`, `W'dual`, `Φhat`, it gives `c`, `WR`, `WR'`, `ΦR`, `DR`, `WC`, `WC'`, `ΦC`, `DC`, `σ₂`,
  `D` with: `c ≠ 0`; the four `Is…PlaceWhittaker` conditions; the two pointwise factorizations
  of `Φ` and `Φhat` (not used); the factorizations `hfacA`, `hfacB` of the partial integrals on
  `σ₂ < Re s`; the nonvanishing `hinf`, `hinfd` of the archimedean products `Ψ_∞`, `Ψ̃_∞`; and
  the nonvanishing `hDne`, `hDdne` of the local integrals at `S`.
* **Step 2 (local functional equations).** For each real place `v`, apply `hR` to
  `aR v`, `dR v`, `dR' v`, `dRd v`, `dRd' v` with their hypotheses, `DR v`, `WR v`, `WR' v`, `ΦR v`
  and the Whittaker conditions of Step 1; `choose` gives `σR v`, `MR v`, `MdR v` with the
  holomorphy of both integrals on `{σR v < Re s}`, the meromorphy of `MR v`, `MdR v`, their
  agreement with the integrals there, and the functional equation off a discrete set (the two
  integrability clauses are not used). The same at each complex place with `hC` gives `σC w`,
  `MC w`, `MdC w`.
* **Step 3 (witnesses).** `Finite.exists_le` bounds the finitely many `σR v`, `σC w`; let
  `σ = max σ₂ (max a b)` with `a`, `b` these bounds. On `{σ < Re s}` the products of the
  archimedean integrals equal `∏ MR v s · ∏ MC w s`, and the same for the dual integrals
  (`Finset.prod_congr`; facts `hprod`, `hprodd`). The witnesses are `σ`,
  `Z s = c · ∏_v MR v s · ∏_w MC w s`, `Zd s = c · ∏_v MdR v s · ∏_w MdC w s`,
  `κ = (∏_v realMinusOneScalar T' v ^ r) · ∏_w complexMinusOneScalar T' w ^ r` and the `D` of
  Step 1.
* **Clause 1.** `Z`, `Zd` are meromorphic (`MeromorphicOn.const`, `MeromorphicOn.mul`,
  `MeromorphicOn.fun_prod`). For nonvanishing, `hinf σ` gives `s₀` with `σ < Re s₀` and
  `Ψ_∞(s₀) ≠ 0`. By `analyticAt_of_eq_on_halfPlane` each `MR v` and `MC w` is analytic at `s₀`,
  so `Z` is analytic at `s₀` (`Finset.analyticAt_fun_prod`), and `Z s₀ = c Ψ_∞(s₀) ≠ 0` by
  `hprod` and `c ≠ 0`. The Library lemma `EqualSemilocalReduction.eventually_ne_zero_of_analyticAt`
  then gives `Z s ≠ 0` off a discrete set. `Zd` is the same with `hinfd` and `hprodd`.
* **Clause 2 (functional equation).** The local functional equations hold simultaneously off
  a discrete set (`Filter.eventually_all` over the finite types of real and of complex
  places). Taking the product over the real places and over the complex places
  (`Finset.prod_congr`, `Finset.prod_mul_distrib`) and combining them with `c` by
  `mul_combine` gives `infiniteL s · Zd (1 − s) = κ · infiniteEpsilon s · dualInfiniteL (1 − s) · Z s`,
  since the `let`s `infiniteL`, `dualInfiniteL`, `infiniteEpsilon` of (P) are by definition the
  product of the real factors times the product of the complex factors.
* **Clause 3.** `hDne` and `hDdne` of Step 1.
* **Clause 4 (sign).** Let `ζ` with `(D v).HasMinusOneScalar (ζ v)` for `v ∈ S`, that is,
  `HasModelMinusOneScalar` for the functional `(D v).ℓ'`, which is nonzero (`(D v).ℓ'_ne_zero`).
  `h3` applied to `F`, `r`, `T'`, `P'`, `hI'`, `S`, `ψv`, `ζ` and these functionals gives
  `(∏ ω'_v(−1)) (∏ ω'_w(−1)) ∏ ζ_v = 1`. Raising it to the power `r` (`Finset.prod_pow`,
  `mul_pow`, `one_pow`) gives `κ ∏_(v ∈ S) ζ_v^r = 1`.
* **Clause 5 (factorization).** For `σ < Re s`, also `σ₂ < Re s`; rewrite with `hfacA` and
  `hprod` and close by `ring`. The dual factorization is the same with `hfacB` and `hprodd`.

`equalSemilocalFactorization_of_archimedeanSemilocalTheory` applies
`equalSemilocalFactorizationReduction` to the four conjuncts of
`ArchimedeanSemilocalTheoryStatement` named in Section 2.

The theorems use only `propext`, `Classical.choice` and `Quot.sound`.

## 5. The retained premises

The four retained premises are `ComplexEqualFunctionalEquationStatement`,
`RealEqualFunctionalEquationStatement`, `EqualArchimedeanFactorizationStatement` and
`ArchimedeanCentralSignStatement`. Proving them needs the archimedean Rankin–Selberg theory of
Jacquet and Shalika in the Library's normalizations, the factorization of global Whittaker
functions and of the partial integrals into local ones, and the global triviality of the
central character at `−1`; see the Markdown of the three statement modules of Task 7136.
