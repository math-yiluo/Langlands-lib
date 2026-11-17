# Totally complex reduction of the equal-rank factorization premise

Module `Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReductionTC`. Author: Worker 5014.

## 1. Content and status

The published proposition
`Langlands.Global.RankinSelbergGlobal.EqualSemilocalFactorizationTCStatement.{u, uQ}` (module
[`EqualSemilocalReductionTC`](EqualSemilocalReductionTC.md); called (P-TC) here) is the
premise `EqualSemilocalFactorizationStatement` with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`. It is the premise of the
totally complex conditional reduction `equalSemilocalReductionTC`. This module contains, in the
namespace `Langlands.Global.RankinSelbergGlobal`:

* the Prop-valued statement `EqualSemilocalFactorizationReductionTCStatement.{u, uQ}`
  (Section 2), the implication from three published statements of the archimedean theory to
  (P-TC);
* the theorem `equalSemilocalFactorizationReductionTC :
  EqualSemilocalFactorizationReductionTCStatement.{u, uQ}`, which proves it (Section 3);
* the theorem `equalSemilocalFactorizationTC_of_archimedeanSemilocalTheory`, which derives
  (P-TC) from the conjunction `ArchimedeanSemilocalTheoryStatement.{u, uQ}` (Section 4);
* the theorem `equalSemilocalEquationTC_of_archimedean`, which derives the totally complex
  semi-local functional equation `EqualSemilocalEquationTCStatement.{u, uQ}` from the same
  three premises (Section 4);
* two local instances (`IsAffine` and `Smooth` for the `GL_n` scheme) that the statements
  need in order to elaborate, as in the module `EqualSemilocalReductionTC`.

The theorem is a **conditional reduction**. It does not prove (P-TC): its three premises are
open statements, stated in the Library by Task 7136 and proved nowhere in the Library. It is
an intermediate result of Task 7124 in the sense of the "Intermediate results" section of
that task's revision 1.

It is the totally complex companion of `equalSemilocalFactorizationReduction` (module
[`EqualSemilocalFactorizationReduction`](EqualSemilocalFactorizationReduction.md)), which
derives the general premise `EqualSemilocalFactorizationStatement` from four premises. Over a
totally complex field there is no real place, so the fourth premise of that reduction, the
real-place functional equation `RealEqualFunctionalEquationStatement`, is not needed here.

## 2. The statement

`EqualSemilocalFactorizationReductionTCStatement.{u, uQ}` is the implication

```
ComplexEqualFunctionalEquationStatement.{u} →
  EqualArchimedeanFactorizationStatement.{u, uQ} → ArchimedeanCentralSignStatement.{u, uQ} →
    EqualSemilocalFactorizationTCStatement.{u, uQ}
```

with the three premises, all in the namespace `Langlands.Global.RankinSelbergGlobal`:

1. `ComplexEqualFunctionalEquationStatement` (module
   [`ArchimedeanFunctionalEquationStatement`](ArchimedeanFunctionalEquationStatement.md)):
   at a complex place, for equal ranks, the archimedean integral and its dual integral (for
   the Fourier transform of the Schwartz function) converge and are holomorphic on a right
   half-plane `σ < Re s`, agree there with functions `M`, `Md` meromorphic on `ℂ`, and satisfy
   the local functional equation off a discrete set, with the sign
   `complexMinusOneScalar T' w ^ r` (Jacquet 2009, Theorem 2.1).
2. `EqualArchimedeanFactorizationStatement` (module
   [`ArchimedeanFactorizationStatement`](ArchimedeanFactorizationStatement.md)): with the
   binders of the general premise, there are `x`, `x'`, `Φ` and a constant `c ≠ 0`,
   archimedean data and local test data `D v` (`v ∈ S`) such that, for `σ₂ < Re s`, the
   partial integral is `c Ψ_∞(s) ∏_(v ∈ S) (D v).integral s` and the dual partial integral is
   `c Ψ̃_∞(s) ∏_(v ∈ S) (D v).dualIntegral s`, with none of `Ψ_∞`, `Ψ̃_∞`, `(D v).integral`,
   `(D v).dualIntegral` vanishing identically on a right half-plane (Cogdell 2004,
   pp.219–220).
3. `ArchimedeanCentralSignStatement` (module
   [`ArchimedeanCentralSignStatement`](ArchimedeanCentralSignStatement.md)): for scalars
   `ζ_v` (`v ∈ S`) by which `−1` acts on the models of nonzero Whittaker functionals for
   `ψv v⁻¹` on the local components of `P'`,
   `(∏_(v real) ω'_v(−1)) (∏_(w complex) ω'_w(−1)) ∏_(v ∈ S) ζ_v = 1` (Cogdell 2004, p.220).

All three premises quantify over every number field; the proof uses them only at the totally
complex field `F` of the conclusion. They are equal-rank components of the conjunction
`ArchimedeanSemilocalTheoryStatement` (module
[`ArchimedeanSemilocalTheoryStatement`](ArchimedeanSemilocalTheoryStatement.md)):
`ComplexEqual…` is the second conjunct of `ComplexPlaceFunctionalEquationStatement`,
`EqualArchimedeanFactorizationStatement` the second conjunct of
`ArchimedeanFactorizationStatement`, and `ArchimedeanCentralSignStatement` the third
component.

**Provenance.** The statement is internal: an implication between published Library
statements, written for Task 7124 as the totally complex form of
`EqualSemilocalFactorizationReductionStatement`, with the real-place premise dropped. Its
argument follows the sketch "Derivation of `EqualSemilocalFactorizationStatement`" in the
Markdown of `ArchimedeanSemilocalTheoryStatement` (Task 7136), which follows Cogdell 2004,
proof of Theorem 4.1, pp.219–220. The source citations of the three premises are in their own
Markdown.

## 3. The proof of `equalSemilocalFactorizationReductionTC`

The proof is the proof of `equalSemilocalFactorizationReduction` (Section 4 of its Markdown),
with one change: the facts about the real places, which that proof obtains from
`RealEqualFunctionalEquationStatement`, are proved vacuously.

* **Step 0 (no real place).** `hnoreal`: every `v : {v : InfinitePlace F // v.IsReal}` gives
  `False`, since `IsTotallyComplex.isComplex v.1` and `InfinitePlace.not_isReal_iff_isComplex`
  contradict `v.2`.
* **Step 1 (factorization).** Apply the factorization premise `h2` to all binders of (P-TC)
  (it is applied at `F`; the instance `IsTotallyComplex F` is not needed for it). This gives
  `x`, `x'`, `Φ` with their four properties, and after the `let`s gives `c`, `WR`, `WR'`, `ΦR`,
  `DR`, `WC`, `WC'`, `ΦC`, `DC`, `σ₂`, `D` with `c ≠ 0`, the Whittaker conditions, the
  factorizations `hfacA`, `hfacB` of the partial integrals on `σ₂ < Re s`, and the
  nonvanishing facts `hinf`, `hinfd`, `hDne`, `hDdne`.
* **Step 2 (local functional equations).** At the real places, the statement `hRF` lists,
  for each real place `v`, the seven facts that the proof uses: an abscissa `σ` and
  functions `M`, `Md` with holomorphy of `realEqualIntegral` and `realEqualDualIntegral` on
  `{σ < Re s}`, meromorphy of `M`, `Md`, their agreement with the two integrals there, and the
  real-place local functional equation with the sign `realMinusOneScalar T' v ^ r`, in the form
  of `RealEqualFunctionalEquationStatement`. It is proved by `(hnoreal v).elim`, and `choose`
  gives `σR`, `MR`, `MdR` and these facts. At each complex place `w`, the premise `hC` gives
  `σC w`, `MC w`, `MdC w` exactly as in the general proof.
* **Steps 3–4 (witnesses and clauses).** Verbatim from the general proof: a common abscissa
  `σ = max σ₂ (max a b)`; the witnesses `Z s = c · ∏_v MR v s · ∏_w MC w s`,
  `Zd s = c · ∏_v MdR v s · ∏_w MdC w s`,
  `κ = (∏_v realMinusOneScalar T' v ^ r) · ∏_w complexMinusOneScalar T' w ^ r` and `D`;
  meromorphy and codiscrete nonvanishing of `Z`, `Zd` (by the helper
  `EqualSemilocalFactorizationReduction.analyticAt_of_eq_on_halfPlane` and the Library lemma
  `EqualSemilocalReduction.eventually_ne_zero_of_analyticAt`); the archimedean functional
  equation as the product of the local ones combined with `c` (helper
  `EqualSemilocalFactorizationReduction.mul_combine`); the nonvanishing of the local integrals
  at `S`; the sign, from `h3` raised to the power `r`; and the two factorizations, by
  rewriting with `hfacA`, `hfacB` and the products and `ring`. The products over the (empty)
  type of real places are kept as they are; no simplification of them is needed.

Both helpers are imported from the module `EqualSemilocalFactorizationReduction`.

## 4. Corollaries

* `equalSemilocalFactorizationTC_of_archimedeanSemilocalTheory` applies
  `equalSemilocalFactorizationReductionTC` to the three conjuncts `h.1.1.2`, `h.2.1.2`, `h.2.2`
  of `ArchimedeanSemilocalTheoryStatement` named in Section 2.
* `equalSemilocalEquationTC_of_archimedean` composes `equalSemilocalFactorizationReductionTC`
  with the published reduction `equalSemilocalReductionTC :
  EqualSemilocalFactorizationTCStatement → EqualSemilocalEquationTCStatement`.

The theorems use only `propext`, `Classical.choice` and `Quot.sound`.

## 5. The retained premises

The three retained premises are `ComplexEqualFunctionalEquationStatement`,
`EqualArchimedeanFactorizationStatement` and `ArchimedeanCentralSignStatement`. Proving them
needs the archimedean Rankin–Selberg theory of Jacquet and Shalika at the complex places in the
Library's normalizations, the factorization of global Whittaker functions and of the partial
integrals into local ones, and the global triviality of the central character at `−1`; see the
Markdown of the three statement modules of Task 7136.
