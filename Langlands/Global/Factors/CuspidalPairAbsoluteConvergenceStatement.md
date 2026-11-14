# Absolute convergence of partial cuspidal pair Euler products for `Re s > 1`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states three propositions, defines one auxiliary function,
and proves nothing:

- `Langlands.Global.CuspidalPairAbsoluteConvergence.logEulerTerm`;
- `Langlands.Global.CuspidalSelfPairContinuationStatement` (Jacquet–Shalika 1981 I,
  Lemma (5.2));
- `Langlands.Global.CuspidalPairAbsoluteConvergenceStatement` (Jacquet–Shalika 1981 I,
  Theorem (5.3), with the double series from its proof; the entry declaration);
- `Langlands.Global.CuspidalPairAbsoluteConvergenceReductionStatement` (Lemma (5.2)
  implies Theorem (5.3), the route of the source proof).

The module is `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceStatement`. It
reuses the published unramified pair factor
`Langlands.Global.CuspidalPairBoundaryNonvanishing.partialEulerFactor` (module
`Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement`) and the
published `HasUnitaryCentralCharacter` and `OperatorRealization.IsContragredientOf`.
Nothing from those modules is rebuilt. The namespace `CuspidalPairAbsoluteConvergence`
is new. It is separate from the existing namespace `CuspidalPairEulerConvergence` of
`CuspidalPairCompletedEquationReduction`, which holds lemmas about convergence on some
right half-plane.

**Why it is here.** The proof task of
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement` (Task
`c4f0be57-1a49-4a42-b813-4354e297ab3f`) follows Jacquet–Shalika 1981 II, Theorem
(4.1). That theorem uses the absolute convergence of the double series
`l(σ, π × π')` for real `σ > 1`. The task's objective says that TaskHub and the
Library contain no form of this convergence. It asks for a helper module or a
separate statement and proof task. This module is that separate statement. Getz–Hahn
p.309 also cites JS I Theorem (5.3) for the absolute convergence of the global
Rankin–Selberg product for `Re s > 1`.

**Proof targets.** Later proof tasks should prove
`CuspidalSelfPairContinuationStatement`,
`CuspidalPairAbsoluteConvergenceReductionStatement` and, from the two,
`CuspidalPairAbsoluteConvergenceStatement`. Each has universe parameters `u` (the
number field) and `uQ` (the factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4` | JS I | Corollary (2.5) and Remark (2.6)(3), p.515 (PDF 17); end of §4 and (5.1), p.554 (PDF 56); Lemma (5.2), pp.554–555 (PDF 56–57); Theorem (5.3), p.555 (PDF 57); its proof, pp.555–557 (PDF 57–59) |
| `getz-hahn-2024-automorphic-representations` | GH | norm shift and absolute convergence for `Re s > 1`, citing [JS81b, Theorem 5.3], p.309 (PDF 320) |
| `jacquet-shalika-1981-euler-ii` | JS II | Theorem (4.1), p.805 (PDF 30), as the consumer |

JS I is *On Euler products and the classification of automorphic representations
I*, Amer. J. Math. 103 (1981), 499–558. Its registered file is
`/home/taskhub/pilot/literature/Jacquet-Shalika, On Euler products and the
classification of automorphic forms I, Amer. J. Math. 103 (1981), 499-558.pdf` (SHA-256
`c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`). Printed page =
PDF page + 498.

**What the source states.**

- **(5.1)** (p.554). `π` and `π'` are irreducible unitary cuspidal representations of
  `G_r(A)` and `G_p(A)`. `S` is a finite set of places that contains the infinite
  places and every finite place where `π_v` or `π'_v` is ramified. `S` is also large
  enough that, for `v ∉ S`, the largest ideal on which the fixed additive character
  `ψ_v` is trivial is the ring of integers. `A_v` and `A'_v` are the semisimple
  conjugacy classes attached to `π_v` and `π'_v`. Then
  `L(s, π_v × π'_v) = det(1 - q_v^(-s) A_v ⊗ A'_v)^(-1)` (5.1.1). Write
  `A_v = diag(α_1v, …, α_rv)`. By (2.5), `|α_jv| < q_v^(1/2)` for `v ∉ S` (5.1.3). So
  the Euler product `L_S(s, π × π') = ∏_(v ∉ S) L(s, π_v × π'_v)` (5.1.4) converges
  absolutely to an analytic function in some right half-plane.
- **Lemma (5.2)** (pp.554–555). If `π` is an irreducible unitary cuspidal
  representation of `G_r(A)`, then `L_S(s, π × π̃)` has an analytic continuation to
  the half-plane `Re s > 1`.
- **Theorem (5.3)** (p.555). Let `π` and `π'` be automorphic cuspidal representations
  of `G_r(A)` and `G_p(A)`, both unitary. Then the infinite product
  `L_S(s, π × π') = ∏_(v ∉ S) L(s, π_v × π'_v)` is absolutely convergent in the
  half-plane `Re s > 1`. In particular `L_S(s, π × π')` does not vanish for
  `Re s > 1`.
- **Proof of (5.3)** (pp.555–557). Each local factor is
  `exp(∑_(n ≥ 1) tr(A_v^n) tr(A'_v^n) / (n q_v^(ns)))` (5.3.1). So, for `Re s` large,
  `L_S(s, π × π')` is the exponential of the double series
  `∑_(v ∉ S) ∑_(n ≥ 1) tr(A_v^n) tr(A'_v^n) / (n q_v^(ns))` (5.3.2). For `π' = π̃` this
  series has the nonnegative coefficients `|tr(A_v^n)|²` (5.3.3). By Landau's theorem
  on Dirichlet series with nonnegative coefficients and by Lemma (5.2), it converges
  for `Re s > 1`. By Cauchy–Schwarz, the double series (5.3.5) for a general pair
  converges absolutely for `Re s > 1`. Then (5.3.2) shows that the product converges
  commutatively, hence absolutely, for `Re s > 1` (Bourbaki, *Topologie générale*,
  Ch. 8).
- **Corollary (2.5)** (p.515). If `π` is an irreducible admissible representation of
  `G_r` that is unitary, generic and unramified, with class `A`, then every
  eigenvalue of `A` has absolute value `< q^(1/2)`. Remark (2.6)(3) says this applies
  to local components of cusp forms.

## 2. Declarations

Namespace `Langlands.Global`. The field `F` is a number field with
`[CompactSpace (AdeleQuotient F)]`, the instance needed by
`CuspidalOperatorRealization`. Throughout, `S` is a finite set of finite places with
`hP : P.exceptional ⊆ S` and `hP' : P'.exceptional ⊆ S`. For a place
`v : {v : FinitePlace F // v ∉ S}`, `A_v` and `A'_v` are the Satake multisets
`P.spectralSystem.eigenvalues v _` and `P'.spectralSystem.eigenvalues v _`, and
`q_v = residueCardinality v`.

### `CuspidalPairAbsoluteConvergence.logEulerTerm P P' hP hP' v n s`

The value is

`tr(A_v^k) · tr(A'_v^k) · (q_v^(-s))^k / k`, with `k = n + 1`.

Here `tr(A_v^k)` is `P.spectralSystem.powerTrace v _ k`, the sum of the `k`-th powers
of the Satake parameters, and `q_v^(-s)` is `RankinSelberg.spectralPoint q_v s`. The
index `n : ℕ` runs over `0, 1, 2, …`, so `k` runs over the positive integers. For fixed
`s`, the family over `(v, n)` is the double series (5.3.2) and (5.3.5) of JS I.

### `CuspidalSelfPairContinuationStatement`

The hypotheses are:

- a number field `F` and a rank `r`;
- actual cuspidal realizations `T` and `Td` of `GL_(r+1)`;
- `HasUnitaryCentralCharacter T`;
- `Td.realization.IsContragredientOf T.realization`: `Td` realizes the contragredient
  of `T`;
- spectral presentations `P` of `T` and `Pd` of `Td`;
- a finite set `S` of finite places with `P.exceptional ⊆ S` and
  `Pd.exceptional ⊆ S`.

The conclusion: there is `L : ℂ → ℂ` such that

1. `L` is complex differentiable on the open half-plane `{s | 1 < Re s}`;
2. for some real `σ` and every `s` with `σ < Re s`,
   `∑_(v ∉ S) ‖partialEulerFactor P Pd hP hPd v s - 1‖` converges, and the Euler
   product of `partialEulerFactor P Pd hP hPd v s` over `v ∉ S` has value `L s`
   (`HasProd`).

So `L` is a holomorphic continuation of `L^S(s, π × π̃)` from some right half-plane to
`Re s > 1`. The function is determined on `Re s > 1` by the identity theorem, since
that half-plane is connected.

### `CuspidalPairAbsoluteConvergenceStatement` (entry)

The hypotheses are:

- a number field `F` and ranks `r`, `t`;
- actual cuspidal realizations `T` of `GL_(r+1)` and `T'` of `GL_(t+1)`, both with
  `HasUnitaryCentralCharacter`;
- spectral presentations `P` of `T` and `P'` of `T'`;
- a finite set `S` of finite places containing `P.exceptional` and `P'.exceptional`;
- a complex number `s` with `1 < Re s`.

The conclusion has three conjuncts:

1. **double series:** the family `‖logEulerTerm P P' hP hP' v n s‖`, indexed by
   `(v, n) : {v // v ∉ S} × ℕ`, is summable. That is,
   `∑_(v ∉ S) ∑_(k ≥ 1) |tr(A_v^k) tr(A'_v^k) q_v^(-ks)| / k` converges.
2. **absolute convergence of the product:**
   `∑_(v ∉ S) ‖partialEulerFactor P P' hP hP' v s - 1‖` converges.
3. **value of the product:** the Euler product of
   `partialEulerFactor P P' hP hP' v s` over `v ∉ S` converges unconditionally
   (`HasProd`, the limit along finite sets of places) to
   `exp(∑'_(v, n) logEulerTerm P P' hP hP' v n s)`.

Since `exp` never vanishes, conjunct 3 says that `L^S(s, π × π') ≠ 0` for `Re s > 1`.

### `CuspidalPairAbsoluteConvergenceReductionStatement`

`CuspidalSelfPairContinuationStatement.{u, uQ} → CuspidalPairAbsoluteConvergenceStatement.{u, uQ}`.

## 3. Hypotheses and their match with the source

- **Cuspidal realizations.** `CuspidalOperatorRealization` is an actual irreducible
  cuspidal subspace of automorphic forms on `GL_(r+1)`. `r + 1` and `t + 1` are JS's
  `r` and `p`, both at least 1.
- **Unitarity.** JS assume `π`, `π'` unitary. Here the hypothesis is
  `HasUnitaryCentralCharacter`, the convention of the published
  `CuspidalUnitaryLocalUnitarityStatement` and
  `CuspidalPairBoundaryNonvanishingStatement`. Some continuous character of the idele
  class group with values of norm 1 is the central character. The Library proves that
  this makes the realization unitarizable
  (`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`, module
  `Langlands.Automorphic.CuspidalUnitaryForm`). The local components are then unitary
  (the proved `cuspidalUnitaryLocalUnitarity`). The hypothesis cannot be dropped in
  `CuspidalPairAbsoluteConvergenceStatement`. A twist `π|det|^x` with real `x < 0`
  has a non-unitary central character. By the norm shift (GH p.309),
  `L^S(s, π|det|^x × π̃) = L^S(s + x, π × π̃)`. This function has a pole at
  `s = 1 - x`, where `Re s > 1` (GH Theorem 11.7.1, after removing the finitely many
  local factors). Absolute convergence on `Re s > 1` would make it holomorphic there.
  `CuspidalSelfPairContinuationStatement` keeps JS's hypothesis on `T`.
  Its contragredient `Td` has the inverse central character, which is unitary as well.
- **`π̃`.** JS write `π̃` for the contragredient. Here it is any actual cuspidal
  realization `Td` with `Td.realization.IsContragredientOf T.realization`. The proved
  `cuspidalContragredientExistence` (module
  `Langlands.Automorphic.CuspidalContragredientExistenceProof`) gives such a `Td`. The
  proved `cuspidalDualPresentationExistence` gives a presentation of it in every factor
  universe. So the hypotheses of `CuspidalSelfPairContinuationStatement` can be met.
- **The set `S`.** Here `S` is any finite set of *finite* places that contains both
  exceptional sets. Infinite places never enter the finite Euler product. Outside
  `P.exceptional` the presentation supplies a nonzero spherical fixed space and its
  Satake spectrum (`HasSphericalHeckeSpectrum`, module
  `Langlands.Automorphic.LocalSphericalHecke`), so both components are unramified at
  every `v ∉ S`. JS's further condition on `ψ_v` only serves the proof of Lemma (5.2).
  It does not narrow the statements. Let `S₀` be `S` together with the finitely many
  places where `ψ` is not unramified. The products over `v ∉ S` and over `v ∉ S₀`
  differ by finitely many unramified factors `det(1 - q_v^(-s) A_v ⊗ A'_v)^(-1)`.
  For `Re s > 1` each of these factors is holomorphic and nonzero, because
  `|α_iv α'_jv q_v^(-s)| < 1` by Corollary (2.5). The local double series
  `∑_(k ≥ 1) |tr(A_v^k) tr(A'_v^k) q_v^(-ks)| / k` of such a place also converges
  there. So the three conjuncts and the continuation for `S` and for `S₀` are
  equivalent.

## 4. Normalizations

- **Satake parameters.** `HasSphericalHeckeSpectrum a` uses the unitary Satake
  normalization (`CuspidalPairFactorData.md` §4, after Gross 1998). So
  `pairEulerPolynomial a b` evaluated at `q_v^(-s)` is JS's
  `det(1 - q_v^(-s) A_v ⊗ A'_v)` (5.1.1). The power traces of `A_v` are JS's
  `tr(A_v^n)`. With this normalization the half-plane is `Re s > 1`, as in JS I and
  GH p.309.
- **Indexing of the double series.** `logEulerTerm` at `n` is JS's term with exponent
  `n + 1`. This avoids a separate condition `n ≥ 1`.
- **Absolute convergence.** For a product `∏ (1 + u_v)` with every factor nonzero,
  JS's "absolutely convergent" means `∑ |u_v| < ∞`. This is conjunct 2. JS also say
  "commutatively convergent", meaning convergence independent of the order of the
  factors. This is Mathlib's `HasProd` over the finite subsets of the index type, in
  conjunct 3.

## 5. Content beyond the source statements, and provenance

- **Conjuncts 1 and 3 of `CuspidalPairAbsoluteConvergenceStatement`.** Theorem (5.3)
  states conjunct 2 and the nonvanishing. Its proof states conjunct 1, the absolute
  convergence of the double series (5.3.5) for `Re s > 1` (p.556). It states the
  identity (5.3.2) for `Re s` large. It concludes the absolute convergence of the
  product for `Re s > 1` from (5.3.2) and conjunct 1 (pp.556–557). Conjunct 3 is
  (5.3.2) on all of `Re s > 1`. JS II Theorem (4.1) needs the double series directly.
  Its `l(σ, π × π') = ∑_(v ∉ S) ∑_(n ≥ 1) conj(tr A_v^n) tr(A'_v^n) / (n q_v^(nσ))`
  is the double series of the pair `(π̃, π')` at real `σ > 1`, because
  `tr(Ã_v^n) = conj(tr A_v^n)` for unitary `π` (§6, step 2 of the reduction).
  Conjunct 3 identifies it with the logarithm of `L^S(σ, π̃ × π')`.
- **Holomorphy of `L^S` on `Re s > 1`.** It is not stated in
  `CuspidalPairAbsoluteConvergenceStatement`. It follows from conjunct 1 by the
  Weierstrass M-test on `Re s ≥ σ₀ > 1`, since `‖logEulerTerm … v n s‖` is at most
  `‖logEulerTerm … v n σ₀‖` there.
- **The reduction.** `CuspidalPairAbsoluteConvergenceReductionStatement` records the
  structure of JS's proof: Theorem (5.3) follows from Lemma (5.2) and local facts. It
  is stated separately so that the analytic part and the global Rankin–Selberg part
  can be proved independently. It adds no mathematical claim beyond the two
  statements. Both universes are shared, so the reduction proof must find the
  presentation `Pd` of the contragredient in the factor universe `uQ`. The proved
  `cuspidalDualPresentationExistence` does this.
- **Not included.** These statements say nothing about the line `Re s = 1` (that is
  `CuspidalPairBoundaryNonvanishingStatement`, Shahidi 1981 Theorem 5.2), meromorphic
  continuation to `ℂ`, poles, or growth.

## 6. Proof routes (for the proof tasks)

**Lemma (5.2).** JS's proof (p.555) writes the global Rankin–Selberg integral
`I(s, W', W, Φ)` as `A(s) L_S(s, π × π̃)` for `Re s` large. Here `A(s)` is the product
of local integrals at `S`, chosen nonzero at a given `s₀` (JS I (1.5), (3.17)). By
JS I (4.6), `I` is holomorphic for `Re s > 1`. An alternative route goes through the
published, unproved `Langlands.Global.CuspidalPairPoleStatement` (GH Theorem 11.7.1;
proof Task 5921). Twist `T` to be trivial on the split centre. The self-pair
`L^S(s, π × π̃)` does not change under `π ↦ π|det|^x`, `π̃ ↦ π̃|det|^(-x)`. Then
divide the completed function by the archimedean factors and the local factors at
`S`, whose reciprocals are entire. The local factors outside `S` must be identified
with `partialEulerFactor`.

**Reduction.** Follow JS pp.555–557:

1. Expand each local factor as an exponential (5.3.1). This needs
   `|α_iv α'_jv q_v^(-s)| < 1`. The Library has
   `Langlands.RankinSelberg.UnramifiedUnitary.norm_characterValues_lt_sqrt` (module
   `Langlands.Representation.RankinSelberg.UnitaryExponentBound`), Corollary (2.5) for
   unitarizable unramified generic constituents. The proved
   `cuspidalUnitaryLocalGenericity` and `cuspidalUnitaryLocalUnitarity` supply its
   hypotheses for the local components. The weaker bound
   `CuspidalSatakeBound.norm_le_of_hasUnitaryCentralCharacter`
   (`‖α‖ ≤ q_v^(m² + 2m)`) suffices on a far right half-plane. Landau's argument then
   gives the sharp bound for the self-pair a posteriori.
2. For `π' = π̃`, `tr(Ã_v^n) = conj(tr A_v^n)`.
   `CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf` (module
   `Langlands.Automorphic.ContragredientSphericalSpectrum`) gives `Ã_v = A_v^(-1)`. For
   a unitary unramified component, `A_v^(-1)` is the complex conjugate of `A_v` as a
   multiset.
3. Landau's theorem for the Dirichlet series (5.3.3) with nonnegative coefficients,
   with Lemma (5.2), gives convergence for `Re s > 1`. Then Cauchy–Schwarz gives
   conjunct 1 for every pair, and conjuncts 2 and 3 follow by `exp`.

The proof tasks may choose other established routes. Each must record the route it
uses.
