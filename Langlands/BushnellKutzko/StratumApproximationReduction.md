# Reduction of T7 to its source parts

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.4.1) and the
defining sequences (2.4.2), printed pp. 65–66 (PDF pp. 77–78). The derivations
below follow the remarks the source makes after (2.4.1) and (2.4.2), and the start
of its proof of (2.4.1)(i) on printed p. 66.

## The reduction statement

`StratumApproximationReductionStatement` is the proposition

`T3 → T5 → T6 → Pᵢ → Pᵢᵢ → Pᵢᵢᵢ → T7`,

with universe parameters `uF, uV`. Here:

- `T3` is `MinimalCriticalExponentStatement.{uF, uV, uV}` (BK93 (1.4.15)). The
  field universe is `uV`, because it is applied to the generated algebra
  `F[γ] ⊆ End_F(V)`.
- `T5` is `StratumEquivalenceStatement.{uF, uV}` (BK93 (1.5.2), (2.1.4)).
- `T6` is `RefinementStatement.{uF, uV, uV}` (BK93 (2.2.8)), also applied with
  `E = F[γ]`.
- `Pᵢ` is `PureStratumSimpleApproximationStatement.{uF, uV}` (BK93 (2.4.1)(i):
  a simple approximation exists, with e and f dividing those of the pure
  stratum for the stratum it produces).
- `Pᵢᵢ` is `SimpleStratumCorestrictionCongruenceStatement.{uF, uV}`
  (BK93 (2.4.1)(ii)(c)).
- `Pᵢᵢᵢ` is `CriticalDerivedStratumStatement.{uF, uV}` (BK93 (2.4.1)(iii)).
- `T7` is the published `StratumApproximationStatement.{uF, uV}`.

The premises are propositions. T3, T5 and T6 are published Library
statements; `Pᵢ`, `Pᵢᵢ` and `Pᵢᵢᵢ` are statements in their own modules
(`PureStratumSimpleApproximationStatement`,
`SimpleStratumCorestrictionCongruenceStatement`, `CriticalDerivedStratumStatement`).
The Library proves T3, T5, T6, `Pᵢᵢ` and `Pᵢᵢᵢ` (`minimalCriticalExponent`,
`stratumEquivalence`, `refinement`, `simpleStratumCorestrictionCongruence`,
`criticalDerivedStratum`) and has no proof of `Pᵢ` or of T7. The theorem `stratumApproximationReduction` proves
the implication; it uses the published proof `tameCorestriction` (T1) for the
existence of tame corestrictions. Its axioms are `propext`, `Classical.choice`
and `Quot.sound`.

## How each part of T7 is obtained

The second and third conjuncts of T7 are `Pᵢᵢ` and `Pᵢᵢᵢ` themselves. The
existence half of the first conjunct is `Pᵢ` without its divisibility clauses.
The other parts are derived as follows.

**Divisibility for every simple approximation** (`dvd_of_simpleApproximation`).
Let `T` be simple and equivalent to `S`. `Pᵢ` gives a simple `T₀ ~ S` whose `e` and
`f` divide those of `S`. Then `T₀ ~ T`, and T5 gives `e(T₀) = e(T)` and
`f(T₀) = f(T)`. This is the source's remark that, by (2.1.4), the invariants
depend only on the equivalence class.

**Simple ⇒ minimal degree** (`degree_le_of_isSimple`). Let `T` be simple and `U`
pure, both equivalent to `S`. `Pᵢ` applied to `U` gives a simple `T' ~ U` with
`e(T') ∣ e(U)` and `f(T') ∣ f(U)`. T5 gives `e(T) = e(T')` and `f(T) = f(T')`.
By the degree formula below, `[F[T.b]:F] = e f` divides `[F[U.b]:F]`, which is
positive. Hence `[F[T.b]:F] ≤ [F[U.b]:F]`.

**Minimal degree ⇒ simple** (`isSimple_of_degree_minimal`). Let `T = [𝔄,n,r,β]`
be pure, equivalent to `S`, and of minimal degree among the pure strata
equivalent to `S` with the same chain and parameters. Suppose `T` is not simple,
so `k₀(β,𝔄)` is an integer `k ≥ −r`. Put `r' = −k ≤ r`, so `r' < n`.

1. `[𝔄,n,r',β]` is pure with `k₀ = −r'`. `Pᵢ` gives a simple `[𝔄,n,r',γ]`
   equivalent to it, and `Pᵢᵢᵢ` gives `γ.HasSimpleDerivedStratum (β − γ)`.
2. `v_𝔄(β − γ) = −r'`. Indeed `β − γ ∈ 𝔓^{−r'}`. If `β − γ ∈ 𝔓^{1−r'}`, the
   strata `[𝔄,n,r'−1,β]` and `[𝔄,n,r'−1,γ]` would be equivalent and both simple,
   and T5 would give `k₀(β) = k₀(γ) < −r'`, which contradicts `k₀(β) = −r'`.
3. With a tame corestriction `s` for `E = F[γ]` (from T1) and the derived and
   simple strata `D ~ C` from step 1, T6 gives a simple `T'' = [𝔄,n,r'−1,β₁]`.
   Its coset is `β + 𝔓^{1−r'}`, its `e` and `f` are those of
   `E₁ = F[γ, c]` (`c = C.b`), and `k₀(β₁) = max(k₀(γ), k₀(c))`.
4. `T''` is equivalent to the simple stratum `[𝔄,n,r'−1,β]`, so T5 gives
   `k₀(β₁) = k₀(β) = −r'`, `e(T'') = e(β)` and `f(T'') = f(β)`. Since
   `k₀(γ) < −r'`, we get `k₀(c,𝔅) = −r' ≠ −∞`. So `c` is not in the image of
   `E`, and `F[γ] ⊊ E₁`.
5. `e(β) ≠ 0`, and `e(β) = e(E₁)`. The auxiliary invariant is zero outside the
   field case, so `E₁` is a field. Then `[F[β]:F] = e f = [E₁:F] > [F[γ]:F]`.
6. `[𝔄,n,r,γ]` is pure and equivalent to `S`, because `β − γ ∈ 𝔓^{−r'} ⊆ 𝔓^{−r}`.
   Its degree is strictly smaller than that of `T`, which contradicts minimality.

**Defining sequences** (`exists_definingSequence`). This is strong induction on
`n − r`. The sequence is kept on the same lattice chain. For pure `S`, `Pᵢ`
gives a simple `γ₀` at level `r`.

- If `k₀(γ₀) = −n` or `−∞`, the one-term sequence `[γ₀]` satisfies (2.4.2).
- Otherwise `k₀(γ₀)` is an integer `k`. Simplicity gives `k < −r`. T3, applied to
  `E = F[γ₀]` with generator `γ₀`, gives `v_𝔄(γ₀) ≤ k`. Here `F[γ₀] ≠ F`
  because `k₀ ≠ −∞`, and `E` normalizes the order by purity. Since
  `v_𝔄(γ₀) = −n`, we get `−n < k`. So `r₁ = −k` satisfies `r < r₁ < n`. The
  induction hypothesis for the pure stratum `[𝔄,n,r₁,γ₀]` gives a sequence
  `q'`, and the sequence for `S` is `γ₀` followed by `q'` (`Fin.cons`).
- Condition (iv) at the first step holds because `k₀(γ₀) = −r₁` and the
  equivalence `[𝔄,n,r₁,γ₁] ~ [𝔄,n,r₁,γ₀]`. Condition (vi) at the first step is
  `Pᵢᵢᵢ` for `[𝔄,n,r₁,γ₀]`, which is at its critical level, and its simple
  approximation `γ₁`. The later steps come from `q'`.

## Auxiliary results

- `subfieldRamificationIndex_mul_residueDegree`: for a finite extension `E/F`,
  `e(E|F) f(E|F) = [E:F]` for the published constructed invariants. The proof
  applies Mathlib's `Ideal.sum_ramification_inertia_eq_finrank` to `𝔬_E` over
  `𝔬_F`: the only prime over `𝔭_F` is `𝔭_E`; `𝔬_E` is finite (Library instance
  `subfieldIntegers_finite`) and torsion-free, hence flat; and
  `IsFractionRing.finrank_eq` gives `finrank 𝔬_F 𝔬_E = [E:F]`. The residue degree
  `length_{𝔬_F}(𝔬_E/𝔭_E)` is identified with the inertia degree in the private
  lemma `length_quotient_eq_inertiaDeg`.
- `subalgebraRamificationIndex_mul_residueDegree` and
  `elementRamificationIndex_mul_residueDegree` are the same formula for a field
  subalgebra of `End_F(V)` and for `F[b]`. `elementDegree_pos` gives positivity.
- `Stratum.equivalent_of_sub_mem`, `Stratum.sub_mem_of_equivalent`: for strata
  with the same chain and depth, equivalence is `S.b − T.b ∈ 𝔓^{−r}`.
- `LatticeChain.valuation_eq_of_mem_of_notMem`: `v_𝔄(x) = k` when `x ∈ 𝔓^k` and
  `x ∉ 𝔓^{k+1}`.
- `neg_n_le_criticalExponent`: `−n ≤ k₀(γ,𝔄)` for pure `[𝔄,n,r,γ]` with
  `k₀ ≠ −∞`, from T3.

The minimal-degree proof raises `synthInstance.maxHeartbeats` to 400000, for
the instances on `End_{F[γ]}(V)` under the field structure `IsField.toField`.
