# Proof of the decomposition of intertwining operators into rank-one steps

Module `Langlands.Global.AdelicIntertwiningElementaryChainProof`. The theorem
`Langlands.Global.intertwiningElementaryChain` proves the published
`Langlands.Global.IntertwiningElementaryChainStatement` (module
`Langlands.Global.AdelicIntertwiningElementaryChainStatement`) with its hypotheses and universe
unchanged. The module also contains `AdelicGroupPoints.isWeylConjugation_one_id`, the Weyl
conjugation `(1, 𝟙)` of a subgroup to itself.

## Helper modules

* `Langlands.Group.RelativeWeylRankOneChain`: `hasRankOneChain_of_right_minimal`, chains of
  rank-one steps in a finite Coxeter group (Bernstein–Zelevinsky 1977, 6.5).
* `Langlands.Global.AdelicIntertwiningParameterShift`:
  `IsIwasawaCompact.intertwiningOperator_add_parameterRestrict`, invariance of the operator under
  parameters of an ambient parabolic.
* `Langlands.Global.AdelicStandardRootFunctional`: root forms of the family through the maximal
  split torus, their kernels, and their transport by Weyl parameters
  (`exists_parameterRestrict_of_rootFunctional_eq_zero`, `exists_unipotentRoot_weylParameter`,
  `restrict_simple_mem_unipotentRoots`).
* `Langlands.Global.AdelicStandardWeylSteps`: Weyl conjugations between the standard parabolics
  of the family (`exists_normalizerPoints_mul_levi`,
  `mem_standardRelativeWeylGroup_iff_of_isWeylConjugation`, `exists_isWeylConjugation_of_image`,
  `intertwiningOperator_add_of_rootFunctional_eq_zero`,
  `intertwiningOperator_eq_of_eq_mul_levi`).

## Implemented proof

Fix `F`, `G`, `fam`, `K`, `hK`, `I`, `I'`, `(w, c)` and `π` as in the statement.

1. **Coxeter system.** `relativeWeylCoxeter` gives a Coxeter system `cs` on the relative Weyl
   group labelled by the simple roots, realizing the root action, with finitely many simple
   roots and `W_L = standardRelativeWeylGroup (rootSet L)` for every finite set `L`. Write
   `I = rootSet IL` and `I' = rootSet IM` (`exists_rootSet_eq`).
2. **Normalizing representative.** `exists_normalizerPoints_mul_levi` gives `z₀ ∈ M_I(F)` with
   `n₀ = w z₀` a normalizer point; `(n₀, c ≫ Int(z₀)⁻¹)` is a Weyl conjugation
   (`IsWeylConjugation.mul_right_levi`), so `[n₀]` conjugates `W_IL` onto `W_IM`
   (`mem_standardRelativeWeylGroup_iff_of_isWeylConjugation`).
3. **Minimal element.** `exists_right_minimal_decomposition` writes `[n₀] = x u` with
   `u ∈ W_IL` and `x` right `IL`-minimal; `x` still conjugates `W_IL` onto `W_IM`. A lift
   `m₀ ∈ M_I(F)` of `u` (`mem_standardRelativeWeylGroup_iff`) gives the normalizer point
   `n' = n₀ m₀⁻¹` with `[n'] = x`.
4. **Chain.** `hasRankOneChain_of_right_minimal` gives `m`, index sets `L_0 = IL, …, L_m = IM`,
   simple roots `a_t ∉ L_t`, steps `g_t ∈ W_{L_t ∪ {a_t}}` and partial products `x_t` with
   `x_m = x`. The standard indices are `J s = rootSet L_{s+1}`, so that
   `(Fin.cons I J t).val = rootSet L_t` for all `t`.
5. **Lifts of the steps.** Each `g_t` has a normalizer lift `n_t` lying in the rational points
   of the standard Levi of `L_t ∪ {a_t}` (`mem_standardRelativeWeylGroup_iff`). By
   `weylAction_image_rootSet_of_simple_bijection`, `n_t` carries the simple roots of `L_t` onto
   those of `L_{t+1}`, so `exists_isWeylConjugation_of_image` gives `cs t` with `(n_t, cs t)` a
   Weyl conjugation from `P_{J' t}` to `P_{J' (t+1)}`, where `J' = Fin.cons I J`. The steps are
   `ws t = n_t`.
6. **Composites.** `W t` and `C t` are defined by `Fin.induction`: `W 0 = 1`, `C 0 = 𝟙`,
   `W (t+1) = ws t * W t` and `C (t+1) = cs t ≫ C t`, so the recursion holds by definition.
   Each `W t` is a normalizer point. By induction, `(W t, C t)` is a Weyl conjugation from `P_I`
   to `P_{J' t}` (`isWeylConjugation_one_id`, `IsWeylConjugation.comp`), the action of `W t`
   carries the simple roots of `I` into `J' t`, and the class of `W t` is `x_t`.
7. **Retractions.** For every index, `parabolicRadical_isIso_subgroupMultiplication` makes the
   multiplication `M_J × U_J → P_J` an isomorphism, and `leviRetraction` is a retraction of
   `l_J` (`levi_comp_leviRetraction`); `πs t` is that retraction for `J' t`.
8. **Clause 4.** For a step `t` take `α = a_t ∘ f_{J' t}`, a root of the presentation of
   `P_{J' t}` in its unipotent radical (`restrict_simple_mem_unipotentRoots`). With
   `S = rootSet (L_t ∪ {a_t})` (`rootSet_insert`), `J' (t+1) ⊆ S` and `ws t ∈ M_S(F)`, so
   `intertwiningOperator_add_of_rootFunctional_eq_zero` gives the invariance of the step
   operator for all `μ`, `ν` with vanishing root form, with `R = 0`; the regularity hypotheses
   are not used. `exists_unipotentRoot_weylParameter`, applied to `(W t, C t)` and the
   retraction `πs t`, gives the root `β` of `P_I`.
9. **Clause 5.** `J' m = I'`, since both have value `rootSet IM`. The classes of `n'` and `W m`
   are both `x`, so `n'⁻¹ W m` centralizes `T` (`QuotientGroup.eq`) and lies in `M_I(F)`
   (`centralizerPoints_le_levi`). Hence `w⁻¹ W m = z₀ m₀⁻¹ (n'⁻¹ W m)` lies in `M_I(F)`, that
   is `W m = w (z ≫ l_I ≫ p_I)` for a rational point `z` of `M_I`. Then
   `intertwiningOperator_eq_of_eq_mul_levi` gives the equality of the operators of `(w, c, π)`
   and `(W m, C m, πs m)` on left `U_I(𝔸)M_I(F)`-invariant functions, at every `μ` (again
   `R = 0`).

## Sources and provenance

The statement's sources are Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §8.6, pp. 225–226, and
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), registered as
`moeglin-waldspurger-1995-spectral-decomposition`, I.1.7, p. 13, I.1.8 (c), pp. 14–15, and
II.1.6, pp. 87–90.

In Mœglin–Waldspurger I.1.7 the elementary symmetry `s_α` attached to a standard Levi `M` and
a root `α` of its split component is `w₂ w₁`, where `w₁` and `w₂` are the longest elements of
the Weyl groups of `M` and of the standard Levi `M_α ⊃ M` with one more simple root.
I.1.8 (c) writes `w ∈ W(M)` as a product of `ℓ(w)` such symmetries through standard Levis,
where `ℓ(w)` counts the positive indivisible roots of the split component of `M` made negative
by `w`; in that count each elementary symmetry has length one (I.1.7 (a)).

The Lean proof uses the same factors `w₀^{L ∪ {a}} w₀^{L}`, which are also the elementary maps
of Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
registered as `bernstein-zelevinsky-1977-induced-i`, 6.5(3), journal p. 470. It follows
Bernstein–Zelevinsky's recursion 6.5(2)–(4), journal pp. 469–470: induction on the ambient
Coxeter length in the relative Weyl group of the family, removing at each stage the factor
attached to a right descent outside the source index set. The two lengths differ: the ambient
Coxeter length of a factor can exceed one (in type `A₂`, with `L = {1}` and `a = 2`, the factor
is `(s₁ s₂ s₁) s₁ = s₁ s₂`). The proof does not use Mœglin–Waldspurger's inversion count; it
uses only that each step lies in the rational points of the Levi of `L_t ∪ {a_t}` and carries
the simple roots of `L_t` onto those of `L_{t+1}`, which is what clause 4 requires.
