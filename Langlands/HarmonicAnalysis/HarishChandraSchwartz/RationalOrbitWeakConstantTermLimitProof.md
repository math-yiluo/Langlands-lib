# The weak constant term as a limit (Waldspurger, Lemma III.5.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWeakConstantTermLimitProof`.

Main theorem:

```
Langlands.HarishChandraSchwartz.rationalOrbitWeakConstantTermLimit :
  RationalOrbitWeakConstantTermLimitStatement hG hi hν I hKc hPK π C hC mu hsq I' hA
```

This proves the published proposition `RationalOrbitWeakConstantTermLimitStatement` (module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm`) for every
parameter of that module. The universes `u` (field) and `uV` (representation) stay independent.
The axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof takes exactly the
premises of the proposition and adds none:
- the quotient Borel instance;
- the standard cocharacter `ζ`;
- `K0` open and compact, the normal basis `B` and its basis-member clauses;
- `SimultaneousStandardBasisAt`, `FiniteCartanCovering` and `StandardLeviCartanCovering` for
  every `J`.

It uses one helper module, `ParabolicLimitOfAnnihilators`, which is part of the same submission
and has its own Markdown.

## Statement proved

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, 2003, Lemma III.5.1 and its proof, printed pp. 269–270.

Notation:
- `P' = P_{I'}`, `M' = M_{I'}(F)`, `J = rootSet I'`, and `Δ_0 − J` are the simple roots outside
  `J`;
- `A` is the compatible split component and `j = standardComponentHom hA : A(F) → M'`;
- `f_ω` is the orbit coefficient `rationalInducedOrbitCoefficientMap … ψ ω`;
- `c = (f_ω)_{P'}` is `rationalOrbitConstantTerm`, the existing `standardConstantTerm`;
- `w = weakPart j c` and `p = positivePart j c = c − w` (published definitions).

Claim: for every `ψ`, every `ω` and every `m' ∈ M'`,
`a ↦ δ_{U'}(m' j(a))^{-1/2} f_ω(m' j(a)) − w(m' j(a))` satisfies
`TendstoZeroAlongParabolic H_0 (Δ_0 − J)`. Here `H_0` is `rationalComponentH0` and the forms are
`rationalOutsideSimpleForms`.

## Route

Waldspurger writes `φ(a) = c(m a) − w(m a)` as a finite sum `Σ_χ Q_χ(H_M(a)) χ(a)`. In proof
(1) on printed p. 270, every exponent `χ` has real part in the closed positive cone `+ā_P^{G*}`
with the origin removed: a nonzero nonnegative combination of the simple roots in `Δ_0 − J`
(cone notation of I.1, printed p. 239). Exponents on the boundary of the cone are therefore
allowed, for example a single simple root when the cone has rank two. Each such piece tends to
zero as `a →_{P'} ∞`. The Lean proof uses a consequence of this condition rather than the
decomposition. At a strict point `y` (every `⟨α, H_0(y)⟩ > 0` for `α ∈ Δ_0 − J`), a nonzero
nonnegative combination `λ` of these roots satisfies `⟨λ, H_0(y)⟩ > 0`. So translation by `j(y)`
contracts the positive part strictly, boundary exponents included. Step 1 below is the Library's
form of this strict contraction at interior chamber points. The Lean proof uses three inputs.

1. **Annihilators** (exponent information). At every strict point `y ∈ C_A^{++}`, the positive
   part `p` is annihilated by a monic polynomial in right translation by `j(y)` whose roots have
   modulus `≤ θ < 1`.
2. **Coefficient bound**: `|f_ω| ≤ c Ξ`.
3. **Invariance**: `Ξ` and `δ_{U'}` are invariant under the lattice points that are central in
   `G(F)`.

The abstract criterion `tendstoZeroAlongParabolic_of_strictAnnihilators` (helper module) combines
these inputs. The limit is proved for `a ↦ p(m' j(a))`. That function agrees with the target
function on a translate of the cone.

## Declarations in this module

### Section `Coordinates`

- `one_lt_residueCardinality_real`: `1 < q`.
- `rationalComponentH0_mul`, `rationalComponentH0_pow`: `H_0` is additive on `A(F)`. Proof:
  `H_0` is the `toAdd` of the homomorphism `rationalComponentValuation`.
- `characterNorm_componentCharacterRestriction_eq_rpow`: `|α|_A(x)| = q^{-⟨α, H_0(x)⟩}`.
  - Reduce to the character norm of `α` on `S` at the image of `x` (unfold the definitions).
  - Then apply `RenardLeviCones.characterNorm_eq_rpow` and `eval_rationalComponentH0`.
- `eval_rationalComponentH0_eq_zero_of_mem_kernel`: on the common norm kernel of `A(F)` every
  coordinate `⟨α, H_0⟩` is `0`. Proof: the character norm there is `1`
  (`mem_rationalCommonNormKernel`), so `q^{-⟨α,H_0⟩} = 1`; take `logb`.
- `eval_rationalComponentH0_of_mem_kernel`: if `x · ϖ^{-c}` lies in the norm kernel, then
  `⟨α, H_0(x)⟩ = ⟨α, q_* c⟩`. Proof: additivity together with
  `eval_rationalComponentH0_latticeSection`.
- `mem_standardCone_of_eval_gt`: suppose `⟨α, H_0(x)⟩ > −log_q ε` for every `α ∈ Δ_0 − J`. Then
  `x ∈ standardCone ε`, the cone of `IsStandardConstantTerm`. Proof: `Real.lt_logb_iff_rpow_lt`.
- `mem_CAstrict_of_eval_pos`: if `x ∈ C_A` and all these coordinates are positive, then
  `x ∈ C_A^{++}` (`CAstrict` for `standardParabolicComponentCharacters`).

### Section `Generators`

- `mem_rationalOutsideSimpleForms`, `eval_mem_rationalOutsideSimpleForms`: the forms are exactly
  the evaluations `eval r` of the roots `r ∈ Δ_0 − J`.
- `exists_rationalComponentH0_generators`: there are a common `d > 0` and, for each form `β`, a
  point `h β ∈ C_A` such that `β(H_0(h β)) = d` and `α(H_0(h β)) = 0` for every other form `α`.
  Construction for a root `r ∈ Δ_0 − J`:
  - The published `standardCocharacter`, applied to `Δ_0 − {r}`, gives `ζ_r` that pairs to zero
    with `Δ_0 − {r}` (so with `J`) and positively with `r`.
  - `IsCompatibleStandardSplitComponent.exists_cocharacter_lift_of_annihilates` lifts `ζ_r` to a
    cocharacter `e_r` of `A`.
  - Let `n_r = ⟨r, q_* e_r⟩ > 0`. Then `h β = ϖ^{(∏_{t ≠ r} n_t) e_r}` with `eval r = β`, and
    `d = ∏_r n_r`. Each root is chosen with `choose!`.

### Section `ShellBound`

- `map_latticeSection_mem_center`: let `c` be a cocharacter of `A` with `⟨r, q_* c⟩ = 0` for all
  `r ∈ Δ_0 − J`. Then the image of `ϖ^c` in `G(F)` is central and lies in `P_0(F)`.
  - The image is the uniformizer power `ϖ^{q_* c}` (`uniformizerSection_naturality`).
  - Its pairings with the roots in `J` vanish by `IsCompatibleStandardSplitComponent.latticePairing_eq_zero`.
  - Centrality: `uniformizerPowers_mem_center_of_simpleRootPairing_eq_zero` with
    `relativeRootNegation`.
  - Membership in `P_0(F)`: `uniformizerPowers_mem_standardLevi` for `∅`.
- `standardRadicalModulus_eq_one_of_mem_center`: `δ_{U_J}(z) = 1` for `z` central in `G(F)`.
  Unfold `closedRestrictCharacter`, then apply `closedNormalizerCharacter_eq_one_of_commute`.
- `exists_bound_halfModulus_rationalXi`: for `m ∈ M_J(F)`, the function
  `y ↦ ‖δ_{U_J}(m j(y))^{-1/2}‖ · Ξ(m j(y))` is bounded above on every shell
  `{R₀ < ⟨r, H_0(y)⟩ ≤ B, r ∈ Δ_0 − J}`. This applies the helper lemma
  `exists_bound_of_latticeSection` with the following data:
  - topology on `A(F)`: the rational-point topology;
  - `N`: the common norm kernel, which is compact (`SplitTorus.isCompact_commonNormKernel`);
  - decomposition `x = n · ϖ^c`: `isUniformizerLatticeSection`;
  - coordinates: `eval_rationalComponentH0_of_mem_kernel`;
  - continuity: `continuous_rationalXi`, the continuity of `j` (`continuous_rationalPointMap`),
    and `continuous_of_mul_right_invariant` for `δ` (its kernel is open by
    `isOpen_ker_standardRadicalModulus`);
  - invariance: for central lattice points `z`, `δ(m j(x) z) = δ(m j(x))` by the previous lemma,
    and `Ξ(g z) = Ξ(z g) = Ξ(g)` by `rationalXi_mul_of_mem_center`.

### Section `Main`: `rationalOrbitWeakConstantTermLimit`

After the premises are introduced:

1. **Annihilators.**
   - The Xi upper bound is unconditional:
     `rationalXiUpperBound_of_jacquetUnipotent rationalMinimalInducedJacquetUnipotent`.
   - So `hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_xiUpperBound` gives, at every
     `y ∈ C_A^{++}`, uniform split annihilators of the constant terms of `ψ`. The covering
     premise is used at `rootSet I`.
   - This step also uses `hsq`, square integrability modulo `C`. Internally, the Library lemma
     calls `hasStandardUnitaryJacquetContraction_of_xiUpperBound` (module
     `RationalOrbitJacquetContraction`). That lemma uses
     `hasXiBoundedCoefficients_standardUnitaryInduced`: every smooth matrix coefficient of every
     unitary induced fiber is bounded by `Ξ`. That bound is built from the inducing-Levi bound
     `hasXiBoundedCoefficients_standardLeviProjectedCompact`, whose transfer from `C` is
     described under "Notes on the requirements".
2. **Constant-term identity.**
   - `rationalOrbitConstantTermExistence` and `HasStandardConstantTerm.isStandardConstantTerm`
     give `ε > 0` such that `δ^{-1/2}(m' j(y)) f_ω(m' j(y)) = c(m' j(y))` on `standardCone ε`.
   - By `mem_standardCone_of_eval_gt` this holds whenever all coordinates exceed
     `R₁ = −log_q ε`.
3. **Reduction to the positive part.** On that region the target function equals `p(m' j(a))`,
   since `p = c − w` by definition. So `TendstoZeroAlongParabolic.congr_of_forall` (with `R₀ = R₁`)
   reduces the goal to the limit of `a ↦ p(m' j(a))`.
4. **Abstract criterion.** Apply `tendstoZeroAlongParabolic_of_strictAnnihilators` with
   `T = C_A` and `HM = H_0` (additive). Its hypotheses are supplied as follows.
   - *Annihilators at strict points.* A point `y ∈ C_A` with positive coordinates lies in
     `C_A^{++}`. Step 1 gives `pp ω` with `pp ω (ρ(j y)) p = 0`. It is transported to
     `a ↦ p(m' j(a))` by `aeval_rightFunctions_comp_eq_zero`, using
     `m' j(y x) = (m' j(y)) j(x)`.
   - *Strict point `g₀`.* `exists_rationalComponentH0_strict`.
   - *Generators.* `exists_rationalComponentH0_generators`.
   - *Deep-shell bound (`R₀ = R₁`).* Fix `B`. The annihilators at `g₀` and
     `exists_norm_le_sum_translates` give
     `|w(x)| ≤ C_w Σ_{k < K} |c(x j(g₀)^k)|` with `c = w + p` (`weakPart_add_positivePart`).
     - For `a` in the shell `(R₁, B]`, each `a g₀^k` (`k < K`) lies in the shell
       `(R₁, B + K M₀]`, where `M₀ = Σ_r ⟨r, H_0(g₀)⟩` and every coordinate of `g₀` is positive.
     - On that shell, step 2 and `|f_ω| ≤ c_ξ Ξ` give `|c(m' j(y))| ≤ c_ξ C_Φ`. The bound
       `|f_ω| ≤ c_ξ Ξ` is
       `exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi_of_squareIntegrable`, from
       square integrability modulo the supplied central subgroup `C`. `C_Φ` comes from
       `exists_bound_halfModulus_rationalXi`.
     - Hence `|p(m' j(a))| ≤ |c| + |w| ≤ c_ξ C_Φ + |C_w| K c_ξ C_Φ`.

## Notes on the requirements

- The arbitrary central subgroup `C` and `hsq` enter through two published Xi bounds:
  - the bound on all coefficients of each unitary induced fiber,
    `hasXiBoundedCoefficients_standardUnitaryInduced`, used by the annihilators of step 1
    through `hasStandardUnitaryJacquetContraction_of_xiUpperBound`;
  - the orbit-section bound
    `exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi_of_squareIntegrable`, used by
    the deep-shell estimate of step 4.

  Both rest on the same inducing-Levi bound `hasXiBoundedCoefficients_standardLeviProjectedCompact`
  (`StandardLeviOriginalOrbitXiBound`). That bound comes from
  `hasXiBoundedCoefficients_standardLeviArbitraryCompact` (`StandardLeviArbitraryCompactXi`).
  This lemma moves `C`, `mu` and `hsq` to the Levi scheme and applies
  `hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable`
  (`GlobalSquareIntegrableCoefficientBound`) with the split component of that Levi scheme. That
  lemma passes from square integrability modulo `C` to square integrability modulo this actual
  split component, via
  `isSquareIntegrable_splitComponent_of_centralSubgroup` (`CentralSubgroupSquareIntegrabilityTransfer`).
  The latter transfers through the full center, using `isSquareIntegrableModCentralSubgroup_transfer`.
  This module proves no comparison between `C` and a split center itself.
- The invariance of `Ξ` and `δ` in the shell bound uses elements central in `G(F)`, built here
  from central lattice directions (`map_latticeSection_mem_center`). It does not involve `C`.
- The weak part is the existing `weakPart` of the existing `standardConstantTerm` (through
  `rationalOrbitWeakConstantTerm`), not a witness of the limit.
- Every standard index `I'` is covered by the same argument, including the improper parabolic
  (no simple roots outside `J`). In that case there are no forms, and the abstract criterion
  shows that the bounded function `a ↦ p(m' j(a))` is zero.

## Check

`lean_check`, modules
`ParabolicLimitOfAnnihilators` and `RationalOrbitWeakConstantTermLimitProof`, declaration
`Langlands.HarishChandraSchwartz.rationalOrbitWeakConstantTermLimit` (lake-build): 0 errors, 0 warnings,
axioms `propext`, `Classical.choice`, `Quot.sound`, level parameters `u`, `uV`.
