# Proof of Springer's Siegel-set overlap estimate for split groups

Author: Worker 2.

This module proves the published statement
`Langlands.Global.AdelicSiegelFactors.SplitSiegelOverlapStatement` (module
`Langlands.Global.AdelicSplitSiegelOverlap`). The theorem is
`splitSiegelOverlap : SplitSiegelOverlapStatement.{u}`. That statement is the
split case of Springer, *Reduction theory over global fields* (1994),
Proposition 2.6 (printed p. 213). Let `G` be split connected reductive over a
number field, `C ⊆ G(A)` compact, `c` a bound for the simple-root norms and `α`
a simple root. Then there is `d > 0` such that two factorizations
`x i(s) p q = x' i(s') p' q'` with `|α(s)| ≤ d` force `q' q⁻¹` into the rational
points of the maximal standard parabolic `P_(Δ ∖ {α})`.

The proof follows Springer's strategy of Bruhat decomposition, heights of a line
fixed by a maximal parabolic, and Weyl-group combinatorics. It does not use
Springer's claim that the line weight is a multiple of `α`, which is false in
higher rank (see `notes/errata/springer-1994-reduction-global-fields.md`). It
uses only the properties proved in `MaximalParabolicLineDominance`: the weight is
fixed by `W_(Δ ∖ {α})` and pairs positively with `α`. Both height inequalities,
one for `γ` and one for `γ⁻¹`, are combined in logarithmic coordinates.

## Logarithmic coordinates

In namespace `Langlands.Global.AdelicSiegelFactors`:

* `torusLog t : characterLattice T →+ ℝ` is the published additive map
  `characterLog F T.toGrp t`. `torusLog_apply` shows that its value at `χ` is
  `log |χ(t)|`, where `|·|` is `PositiveRealTorus.normCharacter`.
* `normCharacter_coe_pos`: character norms are positive reals.
* `torusLog_le_of_normCharacter_le`: `|χ(t)| ≤ c` implies
  `torusLog t χ ≤ log (max c 1)`.
* `exists_torusLog_le_of_mem_closure`: if `χ` is a sum of elements of a set `Δ`,
  there is `N` such that every `t` with `|β(t)| ≤ c` for all `β ∈ Δ` satisfies
  `torusLog t χ ≤ N · log (max c 1)`. The proof is induction on closure
  membership; `N` counts summands.
* `exists_uniform_torusLog_le`: the same bound, with one `N` for a finite family
  of such characters (the supremum over the family).

## The main proof

Fix `F, G, T, i, ν, C, c` and the simple root `α`, written as a label
`a : SimpleRoot i ν`.

1. *Combinatorial and representation data.* The published `relativeWeylCoxeter`
   gives finiteness of the relative Weyl group and a Coxeter realization `cs`.
   `exists_maximalParabolic_dominant_line` gives a matrix representation `ρ`
   and a coordinate line, preserved by `P_∅` and the torus, with torus character
   `ψ`. The published `standardCocharacter` gives a standard cocharacter `ζ` for
   `Δ ∖ {α}`. The realization supplies the reflection of `α` in the form
   `χ ↦ χ - f(χ) • α` with `f(α) = 2`, and dominance gives `f(ψ) > 0`. Hence
   `ψ - s_α ψ = f(ψ) • α` with `f(ψ)` a positive natural number, and `ψ` is fixed
   by the simple reflections other than `s_α`.
   `DominantDisplacement.displacement_mem_closure` then shows two things for
   every Weyl element `w`. First, `ψ - wψ` is a sum of simple roots. Second, if
   `w ∉ W_(Δ ∖ {α})`, then `ψ - wψ - α` is also a sum of simple roots.
2. *Constants.* Apply `exists_uniform_torusLog_le` to these two finite families,
   indexed by the Weyl group and by its elements outside `W_(Δ ∖ {α})`. This
   gives `N₁` and `N₂`. `exists_bruhat_height_bound` (module
   `AdelicSplitOverlapHeight`) gives a height constant `D > 0` for `ρ` and `C`.
   With `lc = log (max c 1)` and `K₀ = 2 log D + (N₁ + N₂) lc`, the threshold is
   `d = exp(-K₀ - 1)`.
3. *Bruhat decomposition.* From `x i(s) p q = x' i(s') p' q'`, the factorizations
   are related by `γ = q' q⁻¹` on one side and by `γ⁻¹` on the other. The
   published `rationalBruhat`, together with
   `standardParabolic_empty_eq_dynamic_of_generic`, writes
   `γ = b₁ n b₂` with `b₁, b₂ ∈ P_∅(F)` and `n` normalizing the torus. Then
   `γ⁻¹ = b₂⁻¹ n⁻¹ b₁⁻¹`. Let `w` be the Weyl class of `n`. Applying the height
   bound to both factorizations and taking logarithms gives
   `torusLog s' (wψ) ≤ log D + torusLog s ψ` and
   `torusLog s (w⁻¹ψ) ≤ log D + torusLog s' ψ`.
4. *`w ∈ W_(Δ ∖ {α})`.* Suppose not. Then `w⁻¹ ∉ W_(Δ ∖ {α})` either. The root
   bounds on `s'` and on `s` give
   `torusLog s' (ψ - wψ) ≤ N₁ lc` and
   `torusLog s (ψ - w⁻¹ψ - α) ≤ N₂ lc`. Adding the four inequalities gives
   `torusLog s α ≥ -K₀`. But `|α(s)| ≤ d` gives `torusLog s α ≤ -K₀ - 1`, a
   contradiction.
5. *Conclusion.* By the published `mem_standardRelativeWeylGroup_iff`, `w` has a
   normalizing representative `n'` in the standard Levi of `Δ ∖ {α}`. Then
   `n'⁻¹ n` centralizes the torus, so it lies in that Levi by the published
   `torusCentralizer_le_standardLevi`. Hence `n` lies in the Levi. The published
   parabolic order puts `P_∅` inside `P_(Δ ∖ {α})`, and the Levi lies in its
   parabolic, so `γ = b₁ n b₂ ∈ P_(Δ ∖ {α})(F)`. Representability of
   `Standard.parabolicHom` produces the required rational point `r` of the
   parabolic scheme, with image `q' q⁻¹`, by `basePointEquiv_comp`.

The hypotheses that `i(s)` and `i(s')` have ambient norm one are not used. The
root bounds on both `s` and `s'`, and the norm-one conditions on `p` and `p'`
(through the height comparison), are used.

## Provenance

The theorem proves an existing Library statement, whose Markdown records its
source: Springer, *Reduction theory over global fields* (1994), Proposition 2.6,
printed p.213 (PDF p.7). The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`. The proof
route is derived. It follows Springer's outline (Bruhat decomposition, heights
of a line fixed by a maximal parabolic, Weyl combinatorics), but replaces the
step corrected in the errata note with the dominance argument above. The
helper modules `DominantWeylDisplacementRoots`, `MaximalParabolicLineDominance`,
`AdelicNormalizerConjugation` and `AdelicSplitOverlapHeight` are internal
infrastructure for this proof. `torusLog` is an internal abbreviation of the
published `characterLog`.
