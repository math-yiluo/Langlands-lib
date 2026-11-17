# The unequal-rank semi-local functional equation from the archimedean theory

This module proves two conditional statements in the namespace
`Langlands.Global.RankinSelbergGlobal`. Both are Prop-valued.

* `UnequalSemilocalArchimedeanReductionStatement.{u, uQ}` is

  `ArchimedeanSemilocalTheoryStatement.{u, uQ} → UnequalSemilocalEquationStatement.{u, uQ}`.

  It is proved as `unequalSemilocalArchimedeanReduction`.
* `UnequalSemilocalComplexReductionStatement.{u, uQ}` is the version for totally complex
  fields:

  `ComplexSemilocalTheoryStatement.{u, uQ} → UnequalSemilocalEquationTCStatement.{u, uQ}`.

  It is proved as `unequalSemilocalComplexReduction`.

The hypotheses are the published statements of the module
`Langlands.Global.RankinSelberg.ArchimedeanSemilocalTheoryStatement`:

* `ArchimedeanSemilocalTheoryStatement` is the conjunction of three results. Result 1 is the
  archimedean local functional equations at the real and the complex places. Result 2 is
  the factorization of the partial integrals over `S` and the infinite places. Result 3 is
  the central sign.
* `ComplexSemilocalTheoryStatement` is the same conjunction with result 1 at the complex
  places only.

Neither hypothesis is proved in the Library, so both results are conditional. They do not
prove `UnequalSemilocalEquationStatement` or `UnequalSemilocalEquationTCStatement`. They
reduce these targets to the archimedean statements, through the published premises
`UnequalSemilocalFactorizationStatement` and `UnequalSemilocalFactorizationTCStatement`.
The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Only the unequal-rank parts of the hypotheses are used:

* `ComplexUnequalFunctionalEquationStatement`;
* `RealUnequalFunctionalEquationStatement`, in the first statement only;
* `UnequalArchimedeanFactorizationStatement`;
* `ArchimedeanCentralSignStatement`.

The equal-rank parts are not used.

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3). The relevant parts are
  the proof of Theorem 4.1 (printed pp.219–220) and §3.2, Theorems 3.5–3.6 (printed
  pp.216–217). In the proof of Theorem 4.1, the global integrals factor over `S` and the
  infinite places, the local functional equations are applied at each of these places, and
  the factors `ω'_v(−1)^(n−1)` cancel in the product.
* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg`: Theorem 2.1. This is the source of result 1.

The module formalizes how the three results combine into the premise. This combination is
the step "by the local functional equations at the places of `S` and at infinity" of
Cogdell's proof, applied to the archimedean part of the premise. The finite places of `S`
are handled in the published reduction `unequalSemilocalEquation_of_factorization`, which
uses the Library's local gamma factors there.

## Proof

### The premise at one number field: `factorization_at`

The theorem `factorization_at` takes three hypotheses:

* `hCo : ComplexUnequalFunctionalEquationStatement`;
* `hFac : UnequalArchimedeanFactorizationStatement`;
* `hSign : ArchimedeanCentralSignStatement`.

It also takes a number field `F`, and a function
`hRe : {v : InfinitePlace F // v.IsReal} → RealUnequalFunctionalEquationStatement`. The
real-place equation is therefore needed only if `F` has a real place.

Its conclusion is the body of `UnequalSemilocalFactorizationStatement` at `F`, restated
verbatim. Like the premise, the statement is elaborated with classical decidability
(`open Classical in`). That is how the products over the real and the complex places get
their `Fintype` instances.

The proof introduces all the binders of the premise. It then proceeds as follows.

1. **Result 2.** `hFac` is applied to the same data, with the given `ψv` and `νv`. It gives:
   * vectors `x`, `x'` that are spherical outside `S`;
   * a constant `c ≠ 0`;
   * archimedean restrictions `WR v`, `WR' v`, `WC w`, `WC' w` and quotient measures
     `DR v`, `DC w`;
   * a real `σ₂` and local test data `D v` at the places `v ∈ S`;
   * the factorizations of the partial and the dual partial integrals, for `σ₂ < Re s`;
   * the nonvanishing clauses.

   The premise asks for the same `x`, `x'` and `D`.
2. **Result 1, place by place.** At each real place `v`, `hRe v` is applied to
   `DR v`, `WR v` and `WR' v`. At each complex place `w`, `hCo` is applied to `DC w`,
   `WC w` and `WC' w`. The tactic `choose` extracts, for each place:
   * an abscissa `σR v` or `σC w`;
   * meromorphic functions `MR v` and `MdR v`, or `MC w` and `MdC w`;
   * the holomorphy of the local integrals on their half-planes;
   * the equalities of these functions with the local integrals on the half-planes;
   * the local functional equations off a discrete set.
3. **A common half-plane.** There are finitely many infinite places, so
   `Finite.exists_le` bounds the `σR v` by some `σR'` and the `σC w` by some `σC'`. The
   premise's `σ` is `max σ₂ (max σR' σC')`.
4. **The archimedean functions.** The proof sets
   * `Ainf s = c · ∏_v MR v s · ∏_w MC w s`;
   * `Binf s = c · ∏_v MdR v s · ∏_w MdC w s`.

   Both are meromorphic on `ℂ`, as products of meromorphic functions
   (`MeromorphicOn.fun_prod`). For `σ < Re s` they equal `c` times the products of the
   local archimedean integrals and of the dual integrals, by `Finset.prod_congr`. With
   result 2, the two factorization clauses of the premise then follow by rewriting.
5. **Nonvanishing off a discrete set.** At every point `s₀` with `σ < Re s₀`, each `MR v`
   and each `MC w` is analytic: on an open half-plane containing `s₀` it agrees with the
   local integral, which is holomorphic there (`DifferentiableOn.analyticAt` and
   `AnalyticAt.congr`). So `Ainf` is analytic at `s₀`. The nonvanishing clause of result 2
   gives such a point `s₀` at which the product of the archimedean integrals is nonzero.
   Since `c ≠ 0`, `Ainf s₀ ≠ 0`. The
   published lemma `EqualSemilocalReduction.eventually_ne_zero_of_analyticAt` then shows
   that `Ainf` is nonzero off a discrete set. The function `Binf` is handled in the same
   way.
6. **Nonzero rational continuations at `S`.** Let `v ∈ S`. The local components are
   generic (`Automorphic.CuspidalPairPartialGamma.localGenericity`). So they have a p-adic
   gamma factor `G` (`RankinSelberg.genericPairGammaFactor_isPadic`). The published lemma
   `PadicUnequalTestData.exists_gammaEquation` then gives a rational function `R` that
   continues the block-zero integral of `D v`. If `R = 0`, the integral would vanish on a
   half-plane `a < Re s`, where `a` is the abscissa of the continuation. This contradicts
   the nonvanishing clause of result 2 for `D v`. So `R ≠ 0`.
7. **The functional equation over the infinite places.** Let `ζ` be scalars with
   `(D v).HasMinusOneScalar (ζ v)` for every `v ∈ S`. The helper lemma
   `exists_inverseFunctional_of_hasMinusOneScalar` turns each of these into what result 3
   needs: a nonzero inverse Whittaker functional with model minus-one scalar `ζ v`, namely
   the inverse functional of `D v`. Result 3 then gives `X · Y · Z = 1`, where
   * `X = ∏_v ω'_v(−1)` over the real places (`realMinusOneScalar`);
   * `Y = ∏_w ω'_w(−1)` over the complex places (`complexMinusOneScalar`);
   * `Z = ∏_(v ∈ S) ζ_v`.

   The local functional equations hold together off a discrete set, since a finite
   intersection of codiscrete sets is codiscrete (`Filter.eventually_all`). Off that set,
   the per-place equations are multiplied together (`Finset.prod_mul_distrib`,
   `Finset.prod_pow`). This gives one equation `hPR` over the real places and one
   equation `hPC` over the complex places. Finally, the algebraic lemma `sign_identity`
   combines `hPR`, `hPC` and `(X · Y · Z)^r = 1` into the premise's equation
   `(∏ ζ_v^r) · L_∞(s) · Binf(1 − s) = ε_∞(s) · L∨_∞(1 − s) · Ainf(s)`. The lemma is
   proved by `linear_combination`.

### Assembling the statements

* `unequalSemilocalFactorization_of_parts` applies `factorization_at` at every number field,
  with the real-place equation as `hRe`. This gives `UnequalSemilocalFactorizationStatement`.
* `unequalSemilocalFactorization_of_archimedean` takes the four parts as projections of
  `ArchimedeanSemilocalTheoryStatement`.
* `unequalSemilocalArchimedeanReduction` composes this with the published
  `unequalSemilocalEquation_of_factorization`.

### Totally complex fields

* `unequalSemilocalFactorizationTC_of_parts` applies `factorization_at` at a totally
  complex field. Such a field has no real place: every infinite place is complex
  (`IsTotallyComplex.isComplex`), hence not real (`InfinitePlace.not_isReal_iff_isComplex`).
  So the function `hRe` is defined by elimination on its empty domain, and the real-place
  equation is not needed.
* `unequalSemilocalFactorizationTC_of_complex` takes the parts as projections of
  `ComplexSemilocalTheoryStatement`.
* `unequalSemilocalComplexReduction` composes this with the published
  `unequalSemilocalEquationTC_of_factorizationTC`.

## Helper declarations

* `exists_inverseFunctional_of_hasMinusOneScalar`: for p-adic test data `D` with
  `D.HasMinusOneScalar ζ`, there is a nonzero inverse Whittaker functional whose model has
  minus-one scalar `ζ`. The witness is `D.inverseFunctional`. The proof only installs the
  instance block of `PadicUnequalTestData`.
* `sign_identity`: for complex numbers, the identities
  `LR · NR = X^r · ER · KR · PR`, `LC · NC = Y^r · EC · KC · PC` and `(X · Y · Z)^r = 1`
  imply `Z^r · (LR · LC) · (c · NR · NC) = ER · EC · (KR · KC) · (c · PR · PC)`.
