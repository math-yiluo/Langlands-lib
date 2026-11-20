# Reduction of Shahidi's boundary nonvanishing to one enlarged set of places

Author: Worker 52, with Worker 3657 (two helper lemmas adapted from their draft for
task `fd17a0f9-9ab1-46d6-a8d9-af3587d0fdcd`, see §4). Contribution to task
`c325654f-b8fb-4a43-9caf-c147e4ae95f2`, revision 1, whose target is the published
`Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`.

**Scope.** The module `Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction`
states one premise, states the reduction, and proves the reduction:

- `Langlands.Global.CuspidalPairBoundaryNonvanishingEnlargedStatement` (the premise,
  not proved here);
- `Langlands.Global.CuspidalPairBoundaryNonvanishingReductionStatement`
  (premise → target);
- `Langlands.Global.cuspidalPairBoundaryNonvanishingReduction` (its proof).

It also proves formal lemmas about the published predicate `IsPartialPairLFunction`:
any two representatives have the same order at every point, and a representative
for a larger set of omitted places gives one for a smaller set of omitted places
without creating zeros.
These are the two arguments that the target's Markdown
(`CuspidalPairBoundaryNonvanishingStatement.md`, §2 and §3) describes in prose. No
analytic input about automorphic forms is used or proved: the premise carries all
of it.

## 1. Sources

"p." is the printed page and "PDF" the page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `shahidi-1981-certain-l` | Sh81 | §2.3, example 1 (the parabolic of `GL_(n+m)` with Levi subgroup `GL_n × GL_m`), pp.324–325 (PDF 29–30); §5, Thm 5.1 and its proof pp.351–352 (PDF 56–57); Thm 5.2 and its proof p.353 (PDF 58) |

The target statement and its Markdown fix all other conventions (Satake
normalization, the unramified factor, the meaning of "nonzero"). This module adds
no convention of its own.

## 2. The premise

`CuspidalPairBoundaryNonvanishingEnlargedStatement.{u, uQ}` has the same binders as
the target:

- a number field `F` with `[CompactSpace (AdeleQuotient F)]`;
- ranks `r`, `t` and cuspidal realizations `T`, `T'`, both with
  `HasUnitaryCentralCharacter`;
- spectral presentations `P`, `P'`;
- a finite set `S` of finite places with `hP : P.exceptional ⊆ S` and
  `hP' : P'.exceptional ⊆ S`.

Its conclusion is: there are a finite set `S₀` of finite places with `hS : S ⊆ S₀`
and a function `L₀ : ℂ → ℂ` such that

1. `IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀`, so `L₀` is a
   meromorphic continuation of the Euler product over the finite places outside
   `S₀`;
2. `meromorphicOrderAt L₀ (1 + y * I) ≤ 0` for every real `y`.

So the premise is the target with two changes. The partial L-function may omit
the factors at finitely many more places. Existence and nonvanishing are asserted
for one representative, not for every representative.

**Match with Sh81.** Sh81 Thm 5.2 (p.353) is proved by applying Thm 5.1 (p.351)
to `G = GL_(n+m)` and the standard maximal parabolic subgroup with Levi subgroup
`M = GL_n × GL_m`. For this parabolic, Sh81 §2.3, example 1 (pp.324–325, PDF
29–30) computes the adjoint action of the L-group of `M` on the Lie algebra of the
dual unipotent radical: it is `ρ_n ⊗ ρ̃_m`, where `ρ_n` is the standard
representation and `ρ̃_m` the dual of the standard representation. Hence for a
representation `π_1 ⊗ π_2` of `M` the attached L-function is
`L(s, π_1 × π̃_2)`, and `a_1 = n + m`. The target's unramified factor
`∏_(i,j) (1 - a_i b_j q_v^(-s))⁻¹`, with `a`, `b` the Satake parameters of `π_v`,
`π'_v`, is the factor of `L(s, π × π')`. So Sh81's argument is applied to the
cuspidal representation `π ⊗ π'^∨` of `M`, where `π'^∨` is the contragredient
of `π'`.

Thm 5.1 needs a finite set `S₁` of places containing the infinite places such that
at every `v ∉ S₁` the representation `π_v ⊗ π'^∨_v` of `M` and the component `χ_v`
of the generic character of the unipotent radical are unramified (Sh81 p.351;
Thm 5.1 also assumes the archimedean components fine, a hypothesis that Thm 5.2
does not restate). Such a set can be chosen to contain any given admissible `S`:
take `S`, the infinite places, and the finitely many finite places where `π`, `π'`
or `χ` ramifies. Its finite part is a set `S₀ ⊇ S` as in the premise. For this
`S₁`, Sh81's proof (pp.351–352) runs as follows. The `χ`-th Fourier coefficient at
the identity of the Eisenstein series, with parameter `s`, is the product of local
Whittaker values at the places in `S₁`, which can be chosen nonzero (Sh81 Props
3.1–3.2), and of `L_(S₁)(1 + (n + m)s, π × π')⁻¹` (Casselman–Shalika at the places
outside `S₁`). A zero of this partial L-function at `1 + (n + m)it` would thus be
a pole of the Fourier coefficient, hence of the Eisenstein series, at the
imaginary point `it`, which the holomorphy of the Eisenstein series on the
imaginary axis excludes (Sh81 p.352; Lapid 2011 Prop 6 in the Library's
formulation, see §5). As `t` runs over
`ℝ`, the point `1 + (n + m)it` runs over the whole line `Re s = 1`, which the
target parametrizes as `1 + y * I`. So Thm 5.1 applies with `S₀` together with the
infinite places, and the premise is the form in which Sh81's argument delivers the
theorem. The reduction proved here supplies the passage from `S₀` to the given
`S`. Sh81 states that passage implicitly by stating Thm 5.2 for every admissible
`S`; the target's Markdown (§3) explains it in prose.

**Why "for every `S` some larger `S₀`".** The premise could have been stated for
`S` itself, or for a single set of places per pair of presentations. The chosen
form is the weakest one from which the reduction goes through with purely formal
arguments, because it only needs the passage from the larger omitted set `S₀` to
the smaller omitted set `S`. That passage multiplies a representative by the
factors `L_v` at the places of `S₀ ∖ S`. Each such factor has order `≤ 0` at every
point, so it cannot raise the order (§3 below); poles of the factors are
harmless. The reverse passage, from `S` to a larger omitted set, divides by the
factors `L_v` and adds their orders with the opposite sign. A pole of `L_v` on
`Re s = 1` would then become a zero. For example, dividing the constant function
`1` by `(1 - q^(1-s))⁻¹` with `q > 1` gives a function with a simple zero at
`s = 1`. That passage therefore needs the local factors at the added places to be
holomorphic on `Re s = 1` (they never vanish, being reciprocals of entire
functions). This is a local bound of Jacquet–Shalika type (`|a_i b_j| < q_v`)
that this module does not use.

## 3. Declarations and what they prove

Namespace `Langlands.Global.CuspidalPairBoundaryNonvanishing`, unless stated
otherwise. Write `L_v(s)` for `partialEulerFactor P P' hP hP' v s`, the unramified
factor `∏_(i,j) (1 - a_i b_j q_v^(-s))⁻¹` of the published statement module.

### Reciprocals of entire functions

- `meromorphicOrderAt_ne_top_of_differentiable`: an entire function that is
  nonzero at one point has finite order (`≠ ⊤`) at every point. This is the
  identity theorem on the connected set `ℂ`, via Mathlib's
  `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`.
- `meromorphicOrderAt_inv_nonpos`: the reciprocal of such a function has order
  `≤ 0` everywhere. Its order is the negative of a nonnegative integer
  (`meromorphicOrderAt_inv`).
- `differentiable_eval_spectralPoint`: for a polynomial `Q` and `q > 0`, the
  function `s ↦ Q(q^(-s))` is entire.
- `exists_eval_spectralPoint_ne_zero`: if `Q(0) = 1` and `q > 1`, this function
  is nonzero at some point. Since `q^(-n) → 0` and `Q` is continuous with
  `Q(0) ≠ 0`, it is nonzero at `s = n` for large natural `n`.
- `pairEulerPolynomial_coeff_zero`: the published `pairEulerPolynomial a b`, a
  product of factors `1 - a_i b_j X`, has constant term `1`.

### The local factors outside `S`

- `differentiable_partialEulerDenominator`: the denominator
  `s ↦ (pairEulerPolynomial a b).eval (q_v^(-s))` of `L_v` is entire.
- `meromorphic_partialEulerFactor`: each `L_v` is meromorphic at every point of
  `ℂ`.
- `meromorphicOrderAt_partialEulerFactor_nonpos`: each `L_v` has order `≤ 0` at
  every point. It is the reciprocal of an entire function that is not
  identically zero, because `q_v > 1` (the published
  `FinitePairFactorChoice.one_lt_residueCardinality`) and the polynomial has
  constant term `1`.

### Uniqueness

These lemmas make precise the uniqueness remark in §2 of the target's Markdown.

- `IsPartialPairLFunction.meromorphic`: a representative is meromorphic at every
  point (the first clause of the predicate, in Mathlib's `Meromorphic` form).
- `IsPartialPairLFunction.meromorphicEq`: two representatives `L`, `L'` for the
  same data satisfy the published `FunctionalEquationComparison.MeromorphicEq L L'`.
  That is, they agree in a punctured neighbourhood of every point. On the
  half-plane `Re s > max σ σ'` both are values of the same convergent product
  (`HasProd.unique`), and the published identity-theorem lemma
  `FunctionalEquationComparison.eq_on_halfplane_meromorphicEq` (module
  `Langlands.Global.Factors.FiniteComparisonProof`) extends the agreement.
- `IsPartialPairLFunction.meromorphicOrderAt_eq`: two representatives have the
  same `meromorphicOrderAt` at every point (`meromorphicOrderAt_congr`).

### Enlarging the set of places

Fix `S ⊆ S₀`, and let `E` be the finite set `S₀.subtype (· ∉ S)` of places outside
`S` that lie in `S₀`.

- `enlargementEquiv hS` (a definition): the equivalence between places outside
  `S` that are not in `E` and places outside `S₀`, given by the identity on the
  underlying place.
- `isPartialPairLFunction_of_superset`: if `L₀` represents the partial L-function
  outside `S₀`, then `s ↦ L₀(s) · ∏_(v ∈ E) L_v(s)` represents the partial
  L-function outside `S`, with the same half-plane. Meromorphy holds because each
  `L_v` is meromorphic. For convergence, the summands outside `E` are those of the
  sum outside `S₀`, transported along `enlargementEquiv`, and the finitely many
  summands in `E` do not affect summability (`Finset.summable_compl_iff`, applied
  to the real-valued norms). For the product, the factors outside `E` have product
  `L₀(s)` by the same transport, and the factors in `E` have the finite product
  `∏_(v ∈ E) L_v(s)`. `HasProd.compl_mul` multiplies the two. It holds in any
  topological commutative monoid, which is needed because `ℂ` under
  multiplication is not a group.
- `exists_isPartialPairLFunction_of_superset`: existence of a representative
  outside `S₀ ⊇ S` gives existence outside `S`.
- `meromorphicOrderAt_nonpos_of_superset`: if `L₀` represents the partial
  L-function outside `S₀ ⊇ S` and has order `≤ 0` at `z`, then every
  representative `L` outside `S` has order `≤ 0` at `z`. By uniqueness,
  `L` has the order of `L₀ · ∏_(v ∈ E) L_v`, which is the order of `L₀` plus the
  orders of the `L_v` (`meromorphicOrderAt_mul`, `meromorphicOrderAt_fun_prod`),
  a sum of nonpositive terms.

### The reduction (namespace `Langlands.Global`)

- `CuspidalPairBoundaryNonvanishingEnlargedStatement`: the premise of §2.
- `CuspidalPairBoundaryNonvanishingReductionStatement.{u, uQ}`: the proposition
  `CuspidalPairBoundaryNonvanishingEnlargedStatement.{u, uQ} →
  CuspidalPairBoundaryNonvanishingStatement.{u, uQ}`, with the same universes on
  both sides.
- `cuspidalPairBoundaryNonvanishingReduction`: its proof. Given the data and `S`,
  the premise gives `S₀ ⊇ S` and `L₀`. The existence conjunct of the target comes
  from `exists_isPartialPairLFunction_of_superset`. The nonvanishing conjunct, for
  an arbitrary representative `L` outside `S` and real `y`, comes from
  `meromorphicOrderAt_nonpos_of_superset` at `z = 1 + y * I`.

## 4. Provenance

- The premise is derived from Sh81 as explained in §2: it is Sh81 Thm 5.2 for the
  set of places that Sh81 Thm 5.1 requires, together with the meromorphic
  continuation that Sh81 takes from Langlands (see §5 of the target's Markdown).
- The uniqueness and enlargement arguments are internal. They formalize the prose
  of §2 and §3 of the target's Markdown, which Worker 3657 wrote.
- `meromorphicOrderAt_inv_nonpos` and `exists_eval_spectralPoint_ne_zero` are
  adapted from Worker 3657's unpublished draft
  `Langlands/Global/Factors/CuspidalIsobaricPoleOrderReduction.lean` (task
  `fd17a0f9-9ab1-46d6-a8d9-af3587d0fdcd`, draft revision 4). The rest is new.

## 5. What is not proved

- The premise `CuspidalPairBoundaryNonvanishingEnlargedStatement` is not proved.
  It contains all the analytic content of Sh81 Thm 5.2 and the meromorphic
  continuation of the partial L-function. Sh81's route to it (pp.351–352, with
  §2.3 pp.324–325 for the parabolic) goes through the `χ`-th (non-constant)
  Fourier coefficient of a cuspidal Eisenstein series on `GL_(n+m)` induced from
  `π ⊗ π'^∨`: its factorization into local Whittaker values, the Casselman–Shalika
  formula at the places outside `S₁` (which gives the factor
  `L_(S₁)(1 + (n + m)s, π × π')⁻¹`), a choice of data making the local Whittaker
  values at the places in `S₁` nonzero (Sh81 Props 3.1–3.2), the inclusion of the
  poles of the Fourier coefficient among those of the Eisenstein series, and
  holomorphy of the Eisenstein series on the imaginary axis.
- Among these inputs, the pinned Library (commit `ecb96e55`) has a published
  statement for the last one:
  `Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` (module
  `Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement`, Lapid 2011
  Prop 6), stated for square-integrable induced forms on a connected reductive
  group scheme over a number field `F : Type` with a parabolic root presentation.
  Its companion `Langlands.Global.EisensteinMeromorphicContinuationStatement`
  (module `Langlands.Global.AdelicEisensteinContinuationStatement`) states the
  meromorphic continuation in the same setting. Neither is proved. Their
  comparison with the cuspidal-pair setting of the target is also outstanding:
  the group `GL_(n+m)`, its maximal parabolic subgroup, an Iwasawa compact
  subgroup and the form induced from the realizations `T`, `T'`, and, for the
  holomorphy statement, the passage from `F : Type` to `F : Type u`. The author
  found no Library statement, in this setting, of the factorization of the
  Fourier coefficient, of the Casselman–Shalika value, or of Sh81 Props 3.1–3.2.
- Hence the target `CuspidalPairBoundaryNonvanishingStatement` is not proved
  here. This module proves only that it follows from the premise.
- Nothing is claimed about holomorphy on `Re s = 1`, about poles, or about zeros
  off the line.
