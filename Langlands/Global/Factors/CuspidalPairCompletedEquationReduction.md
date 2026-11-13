# Reduction of the completed Rankin–Selberg equation of cuspidal pairs

Module `Langlands.Global.Factors.CuspidalPairCompletedEquationReduction`.

## 1. Content and provenance

The published statement `Langlands.Global.CuspidalPairCompletedEquationStatement.{u, uQ}`
(module `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`) concludes
`c.CompletedEquationHolds S Linf Ldinf εinf`. This is the conjunction of:

1. absolute convergence: on some right half-plane `∑_v ‖L_v(s) - 1‖` and `∑_v ‖L∨_v(s) - 1‖`
   converge, where `L_v = c.finiteL v` and `L∨_v = c.finiteDualL v`;
2. both Euler products have values `p` and `pd` there, and `Λ(s) = Linf(s) p`,
   `Λd(s) = Ldinf(s) pd`;
3. `Λ` and `Λd` are meromorphic on `ℂ`;
4. the functional equation `Λ(s) = (∏_(v ∈ S) ε_v(s)) ε_∞(s) Λd(1 - s)` off a discrete set.

This module splits off item 1, together with the existence of the values in item 2, and
proves it from a bound on the Satake parameters. It contains:

* the definitions `CuspidalPairFunctionalEquation.HasSatakeBound` and
  `CuspidalPairFunctionalEquation.FinitePairFactorChoice.ContinuationHolds` (Section 2);
* the statements `CuspidalSatakeBoundStatement`, `CuspidalPairContinuationStatement` and
  `CuspidalPairCompletedEquationReductionStatement` (Section 3);
* the theorem `cuspidalPairCompletedEquationReduction`, which proves
  `CuspidalPairCompletedEquationReductionStatement`, i.e.
  `CuspidalSatakeBoundStatement.{u, uQ} → CuspidalPairContinuationStatement.{u, uQ} →
  CuspidalPairCompletedEquationStatement.{u, uQ}`, and the analytic lemmas it uses
  (Section 4).

The theorem is a reduction: it does not prove the target. The two premises are separate
open statements (Section 5). It is an intermediate result of Task 5721 in the sense of the
"Intermediate results" section of that task's revision 2: it isolates the absolute
convergence of the Euler products, one of the task's listed prerequisites, and leaves the
unconditional proof of the target open.

**Sources.** The argument is the classical one:

* Jacquet–Shalika, *On Euler products and the classification of automorphic forms I*,
  Amer. J. Math. 103 (1981) (Library source
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`),
  Corollary (2.5), printed p.515 (PDF p.17): if `π` is irreducible admissible, unitary,
  generic and unramified, the eigenvalues of its Satake class have absolute value
  `< q^(1/2)`; remark (3) on the same page: this applies to local components of cusp forms.
  §(5.1), printed p.554 (PDF p.56): for unitary cuspidal `π`, `π'` and `v ∉ S`,
  `L(s, π_v × π'_v) = det(1 - q_v^(-s) A_v ⊗ A'_v)^(-1)`; "It follows from (2.5) that"
  every eigenvalue satisfies `|μ_j(ϖ_v)| < q_v^(1/2)`, "Thus it is clear that the Euler
  product `L_S(s, π × π')` converges absolutely to an analytic function in some right
  half-plane."
* Cogdell, *Lectures on L-functions, converse theorems, and functoriality for GL_n*
  (`cogdell-2003-fields-lectures-www`), Corollary 7.1.2, printed p.58 (PDF p.62): the
  Jacquet–Shalika bounds `q^(-1/2) < |μ_i(ϖ)| < q^(1/2)`.
* Getz–Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`), printed p.309 (PDF p.320): after the norm
  shift `π ⊗ |det|^(s_1)` the product (11.23) converges absolutely for `Re(s) > 1`;
  Theorem 11.7.1 (continuation and functional equation).
* Cogdell, *Analytic theory of L-functions for GL_n* (2004)
  (`cogdell-2004-analytic-theory-gln`), Theorem 4.1, printed p.219 (PDF p.222): the global
  theorem whose completed form the target states; Theorem 3.3, printed p.215 (PDF p.218): the
  unramified factors `det(I - q^(-s) A_π ⊗ A_π')^(-1)`.

**Provenance (internal).** The split is not a statement of these sources. It isolates the
convergence argument of Jacquet–Shalika §(5.1):

* `CuspidalSatakeBoundStatement` is a *weakened, derived* form of Corollary (2.5): it asks
  only for some real exponent `C`, depending on the presentation, with `‖α‖ ≤ q_v ^ C` for
  all Satake parameters `α` outside the exceptional set. It makes no unitarity hypothesis.
  It is true for every cuspidal realization: a twist by `|det|^a` with real `a` makes the
  central character unitary and multiplies every Satake parameter by `q_v ^ (± a)`, and a
  normalization of the spectrum by a fixed power of `q_v` (such as `q_v ^ ((n - 1)/2)`)
  changes only `C`. The premise `HasIrreducibleAdmissibleComponents P` is the hypothesis
  under which the target uses `P`.
* `CuspidalPairContinuationStatement` keeps every binder and hypothesis of
  `CuspidalPairCompletedEquationStatement` unchanged (the binder list is copied verbatim,
  with the same `classical` elaboration and the same `let`-definitions of the archimedean
  L- and ε-products). Only the conclusion changes: `ContinuationHolds` asks for items 2–4
  above, with item 2 required only for those `s` at which both Euler products converge.
  This is Cogdell 2004 Theorem 4.1 / Getz–Hahn Theorem 11.7.1 in the completed form of the
  target, with the absolute convergence removed.

## 2. Definitions

* `HasSatakeBound P C` (for `P : CuspidalSpectralPresentation.{u, uQ} T`, `T` of rank
  `r + 1`, `C : ℝ`): for every finite place `v` and `hv : v ∉ P.exceptional`, every
  element `α` of the multiset `P.spectralSystem.eigenvalues v hv` (a `Sym ℂˣ (r + 1)`,
  the Satake parameters of the local component pinned by `P.hasSpectrum`) satisfies
  `‖(α : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ C`.
* `c.ContinuationHolds S Linf Ldinf εinf` (for a finite factor choice `c`): there are
  `σ : ℝ` and `Λ Λd : ℂ → ℂ` with `MeromorphicOn Λ Set.univ`, `MeromorphicOn Λd Set.univ`;
  for every `s` with `σ < s.re` and all `p pd : ℂ`, if
  `HasProd (fun v => c.finiteL v s) p` and `HasProd (fun v => c.finiteDualL v s) pd`, then
  `Λ s = Linf s * p` and `Λd s = Ldinf s * pd`; and
  `∀ᶠ s in Filter.codiscrete ℂ, Λ s = (∏ v ∈ S, c.finiteEpsilon v s) * εinf s * Λd (1 - s)`.
  Compared with `CompletedEquationHolds`, the two `Summable` conjuncts and the existence of
  `p` and `pd` are removed, and the identification is conditional on convergence. The
  meromorphy and functional-equation conjuncts are identical.

## 3. Statements

* `CuspidalSatakeBoundStatement.{u, uQ}`: for every number field `F : Type u` with
  `CompactSpace (AdeleQuotient F)`, every `r`, every actual cuspidal realization
  `T : CuspidalOperatorRealization F r` and every `P : CuspidalSpectralPresentation.{u, uQ} T`
  with `HasIrreducibleAdmissibleComponents P`, there is `C : ℝ` with `HasSatakeBound P C`.
* `CuspidalPairContinuationStatement.{u, uQ}`: the binders and hypotheses of
  `CuspidalPairCompletedEquationStatement` (number field, nontrivial unitary additive
  character `ψ` trivial on `F`, ranks, the four realizations with the two
  `IsContragredientOf` relations, the four presentations with irreducible admissible
  components, `S` containing the four exceptional sets with `FiniteAdditiveSupport ψ S`,
  every factor choice `c` unramified outside `S`, the archimedean additive components `aR`,
  `aC` and parameter lists `dR … dCd'` with their specifications), concluding
  `c.ContinuationHolds S infiniteL dualInfiniteL infiniteEpsilon` with the same
  `infiniteL`, `dualInfiniteL`, `infiniteEpsilon` as the target.
* `CuspidalPairCompletedEquationReductionStatement.{u, uQ}`:
  `CuspidalSatakeBoundStatement.{u, uQ} → CuspidalPairContinuationStatement.{u, uQ} →
  CuspidalPairCompletedEquationStatement.{u, uQ}`.

## 4. The proof

Namespace `Langlands.Global.CuspidalPairEulerConvergence`, local estimates:

* `norm_prod_one_sub_sub_one_le`: for a multiset `M` of complex numbers with `‖z‖ ≤ ε ≤ 1`
  for all `z ∈ M`, `‖∏_(z ∈ M) (1 - z) - 1‖ ≤ (2 ^ #M - 1) ε`. Induction on `M`:
  `(1 - a) Q - 1 = (1 - a)(Q - 1) - a` and `‖1 - a‖ ≤ 2` give
  `2 (2^k - 1) ε + ε = (2^(k+1) - 1) ε`.
* `norm_inv_sub_one_le`: if `‖P - 1‖ ≤ 1/2` then `‖P‖ ≥ 1/2`, and
  `P⁻¹ - 1 = -(P - 1)/P` gives `‖P⁻¹ - 1‖ ≤ 2 ‖P - 1‖`.
* `eval_pairEulerPolynomial`: `pairEulerPolynomial a b` evaluated at `x` is
  `∏_((α, β) ∈ a ×ˢ b) (1 - α β x)` (`Polynomial.eval_multiset_prod`).
* `norm_inv_eval_pairEulerPolynomial_sub_one_le`: if `0 ≤ ε`, `‖α β x‖ ≤ ε` for all pairs
  and `2^(n m) ε ≤ 1/2`, then `‖P(x)⁻¹ - 1‖ ≤ 2^(n m + 1) ε`. The product multiset has
  `n m` elements (`Multiset.card_product`, `Sym.card_coe`); combine the two previous bounds.
* `residueCardinality_eq_absNorm`: `q_v = N(v)`. This is
  `HeckeEulerProduct.residueCardinality_eq`; the residue field of
  `CompletionPadic.topologicalData v` depends only on its valuative relation, which is that
  of `(padicField v).canonicalTopologicalData`, so the two residue cardinalities agree by
  definition. Hence `two_le_residueCardinality` (`NumberField.HeightOneSpectrum.one_lt_absNorm`)
  and `norm_spectralPoint`: `‖q_v ^ (-s)‖ = q_v ^ (-Re s)` (`Complex.norm_natCast_cpow_of_pos`).
* `summable_norm_inv_eval_sub_one`: let `S` be finite and, for `v ∉ S`, `L v` the pair
  Euler polynomial of multisets `a v`, `b v` of sizes `n`, `m` with `‖α‖ ≤ q_v ^ A`,
  `‖β‖ ≤ q_v ^ B`. If `A + B + (n m + 1) < Re s`, then
  `∑_v ‖L_v(q_v ^ (-s))⁻¹ - 1‖` converges. Put `δ = Re s - A - B > n m + 1`. For `v ∉ S`,
  `‖α β q_v^(-s)‖ ≤ q_v ^ (-δ) =: ε_v`, and `ε_v ≤ q_v ^ (-(n m + 1)) ≤ 2 ^ (-(n m + 1))`
  because `q_v ≥ 2`, so `2^(n m) ε_v ≤ 1/2`. The local estimate bounds the term by
  `2^(n m + 1) N(v) ^ (-δ)`, which is summable by `HeckeEulerProduct.summable_absNorm_rpow`
  (`δ > 1`). Since the bound holds for all `v` outside the finite set `S`
  (`Finset.eventually_cofinite_notMem`), `Summable.of_norm_bounded_eventually` concludes.
* `hasProd_of_summable_norm_sub_one`: if `∑ ‖f i - 1‖` converges then
  `HasProd f (∏' i, f i)` (`multipliable_one_add_of_summable` applied to `f i - 1`).

Namespace `Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice`:

* `summable_of_hasSatakeBound`: if `c.IsUnramifiedOutside S`, the four exceptional sets lie
  in `S`, and `HasSatakeBound P A`, `HasSatakeBound P' B`, `HasSatakeBound Pd Ad`,
  `HasSatakeBound Pd' Bd`, then for
  `max (A + B) (Ad + Bd) + ((r + 1)(t + 1) + 1) < Re s` both
  `∑_v ‖c.finiteL v s - 1‖` and `∑_v ‖c.finiteDualL v s - 1‖` converge. Outside `S`,
  `IsUnramifiedOutside` identifies `c.lPolynomial v` (resp. `c.dualLPolynomial v`) with the
  pair Euler polynomial of the Satake multisets of `P`, `P'` (resp. `Pd`, `Pd'`), and
  `c.finiteL v s` is by definition `((c.lPolynomial v).eval (q_v ^ (-s)))⁻¹`; apply
  `summable_norm_inv_eval_sub_one` with `n = r + 1`, `m = t + 1`.
* `completedEquationHolds_of_continuationHolds`: from `ContinuationHolds` with `σ`, `Λ`,
  `Λd`, take the half-plane `Re s > max σ (max (A + B) (Ad + Bd) + ((r + 1)(t + 1) + 1))`.
  There both sums converge, `hasProd_of_summable_norm_sub_one` gives the values
  `p = ∏' v, c.finiteL v s` and `pd = ∏' v, c.finiteDualL v s`, and `ContinuationHolds`
  gives `Λ s = Linf s * p`, `Λd s = Ldinf s * pd`. Meromorphy and the functional equation
  are passed through unchanged.

`cuspidalPairCompletedEquationReduction` introduces all binders of the target, obtains the
four exponents from `CuspidalSatakeBoundStatement` applied to `P`, `P'`, `Pd`, `Pd'`, and
applies `completedEquationHolds_of_continuationHolds` to
`CuspidalPairContinuationStatement` at the same data. The archimedean `let`-definitions of
the two statements are elaborated identically, so they agree definitionally.

## 5. Scope and remaining work

* The half-plane obtained is not the optimal `Re s > 1` of Getz–Hahn p.309; the target only
  asks for some right half-plane.
* `CuspidalSatakeBoundStatement` remains to be proved. A route: twist by `|det|^a` to a
  unitary central character (`Automorphic.cuspidalDeterminantMultiple`), use local
  unitarity of the components (`Automorphic.cuspidalUnitaryLocalUnitarity`), and bound the
  Satake parameters of a unitary unramified irreducible representation, by Jacquet–Shalika
  (2.5) (which also needs genericity of the local components) or by the trivial bound from
  the boundedness of spherical matrix coefficients.
* `CuspidalPairContinuationStatement` carries the remaining obligations of section 8 of
  `CuspidalPairFunctionalEquationStatement.md`: the global Rankin–Selberg theory, the
  comparison of the finite integral factors with the classification factors, the
  archimedean local theory and independence of the parameter lists, the norm shift and the
  sign cancellation.
