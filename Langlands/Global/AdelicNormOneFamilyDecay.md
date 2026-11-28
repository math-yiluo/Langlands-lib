# Iterated decay for families on norm-one points

This module, `Langlands.Global.AdelicNormOneFamilyDecay`, is the analytic step of Arthur's estimate
of alternating constant terms (Arthur, *A trace formula for reductive groups II* (1980), Lemma 1.4
and the estimate (1.2), printed p. 95; *An introduction to the trace formula* (2005), (13.7)–(13.8),
printed pp. 71–72), in a form suited to families of functions of finite regularity indexed by an
arbitrary measure space `(Ω, m)`. Instead of bounding a supremum, every estimate bounds the
**family integral** `∫_Ω ‖g o x‖ dm` at a point `x` by family integrals of derivatives at nearby
points. The route uses mean values along paths instead of Arthur's Fourier expansion on
`N(F) \ N(𝔸)`. All declarations are in `Langlands.Global`.

## Derivatives in integrated form

Let `At` be an embedded Lie atlas on `G(F∞)¹` with tangent space `Fin e → ℝ` at the identity.

`IsNormOnePathDerivative At g g'` (for `g : G(𝔸) → ℂ` and `g' : Fin e → G(𝔸) → ℂ`) states: for
every norm-one point `y`, every path `c : ℝ → G(F∞)¹` smooth for `At` and every continuous `V` with
`leftPathVelocity c t = V t` for all `t`,

`g (y c(1)) − g (y c(0)) = ∫₀¹ ∑_l V(t)_l g' l (y c(t)) dt`.

So `g' l` is the derivative of `g` along the coordinate direction `l` of `G(F∞)¹`, acting on the
right, recorded through the fundamental theorem of calculus; no differentiability of `g` itself is
required. `isNormOnePathDerivative_sum` shows that the identity is preserved by finite linear
combinations when the derivatives are continuous. `mul_ofInfinite_conj` is the identity
`k · (k∞⁻¹ h k∞) = h · k` for `h ∈ G(F∞)` and the archimedean component `k∞` of `k`.

## One step

`normOneFamilyContractionStep` takes a closed smooth connected unipotent subgroup `j : U ⟶ G`, a set
`Ω ⊆ G(𝔸)`, points `a : X → G(𝔸)`, a subgroup `L₀`, a smooth map `Ψ : E → G(F∞)` from a
finite-dimensional real normed space with `Ψ(0) = 1` and values in `G(F∞)¹`, and contraction factors
`0 ≤ ε(t) ≤ Bε`, subject to the contraction hypothesis `HasUnipotentContractionModulo j Ω a L₀ Ψ ε`:
for every compact set `D` of archimedean points of `U` there is `C` such that for `p ∈ Ω`, `t` and
`u ∈ D` there are `v ∈ E` with `‖v‖ ≤ C ε(t)` and `l ∈ L₀` with `u (p a(t)) = l (p a(t) Ψ(v))`. It
also takes a compact set `Yf` of finite adelic points, an open subgroup `L` of `G(𝔸_f)` and a
compact set `K ⊆ G(𝔸)¹`.

The conclusion is a compact `K'` with `K ⊆ K' ⊆ G(𝔸)¹` and a constant `C` with the following
property. Let `p ∈ Ω` and `t` with `p a(t) ∈ G(𝔸)¹`, and `k ∈ K` with finite component of
`p a(t) k` in `Yf`. Let `g o`, `g' o l` be families of continuous functions, jointly measurable in
`(o, x)`, with `g o` left invariant under `U(F)` and `L₀`, right invariant under `L`, with vanishing
constant term along `U`, and with `IsNormOnePathDerivative At (g o) (g' o)`. Then

`∫_Ω ‖g o (p a(t) k)‖ dm ≤ C ε(t) · sup { ∫_Ω ‖g' o l (p a(t) k')‖ dm : k' ∈ K', k'_f = k_f, l }`.

**Proof.** Let `x = p a(t) k`. Since the constant term vanishes, `adelicUnipotentFamilyOscillation`
bounds `∫ ‖g o x‖` by the supremum over a compact set `D` of archimedean points `u` of `U` of
`∫ ‖g o x − g o (u x)‖`. For `u ∈ D` the contraction hypothesis gives `v` and `l ∈ L₀`; by left
invariance under `L₀` and `mul_ofInfinite_conj`, `g o (u x) = g o (x c(1))` for the path
`c(s) = k∞⁻¹ Ψ(s v) k∞` (`conjugatePath`), and `x c(0) = x`. The path is smooth for `At` and its
translated velocity is `conjugateDifferential At Ψ hΨ₁ (k∞, s v) v`
(module `Langlands.Automorphic.GroupSchemeNormOneConjugatePaths`). The derivative identity and
`lintegral_enorm_sub_le_iSup_of_integral` bound `∫ ‖g o (x c(1)) − g o x‖` by the supremum over
`s ∈ [0, 1]` of `∫ ‖∑_l V(s)_l g' o l (x c(s))‖`. The velocity bound
`exists_norm_conjugateDifferential_le` gives `|V(s)_l| ≤ C₁ ‖v‖ ≤ C₁ C ε(t)`, and
`x c(s) = p a(t) (Ψ(s v) k)` with `Ψ(s v) k ∈ K' = Ψ(closed ball) · K` and the same finite
component as `k`. This gives the constant `e C₁ C`.

## Iteration

`normOneFamilyDecayModulo` iterates the step `n` times for a whole system `g o w` indexed by words
`w : List (Fin e)`, where `g o (l :: w)` is the derivative of `g o w` along `l` for words shorter
than `n` (and the constant terms of these vanish). It gives a compact `K'` and `C` with

`∫_Ω ‖g o [] (p a(t) k)‖ dm ≤ C ε(t)ⁿ · sup { ∫_Ω ‖g o w (p a(t) k')‖ dm : k' ∈ K', k'_f = k_f, |w| = n }`.

The induction applies the step to `g o []` and then the induction hypothesis to the shifted systems
`w ↦ g o (w ++ [l])` at the points `k'` produced by the step.
