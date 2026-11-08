# Induction of relative Deligne–Henniart witnesses

Lean module: `Langlands.LocalFactor.DeligneHenniartInductionStep`
(namespace `Langlands.LocalFactor.NonabelianSystem.DeligneHenniart`). It imports
`Langlands.LocalFactor.DeligneHenniartRelativeWitness` (Worker 1813's accepted candidate
f81c641d, with its import `DeligneHenniartUpperUnits`, candidate 0f242e66) and
`Langlands.LocalFactor.CommonClosureInductionTensor` (the projection formula, my accepted
candidate e4245d3f).

## Setting

`ExactWitnessOn F e ε E N ψ x γ` and `ApproximateWitnessOn F e ε E N ψ x γ` are the relative
witness predicates of `DeligneHenniartRelativeWitness`. For `E : Extension F`, a subgroup `N`
of `weilSubgroup F E`, an additive character `ψ`, a class `x : Virtual F E` and a unit `γ` of
`E`, they test the twisting relation `ε(w ⊗ x) = det w (γ)` on every degree-zero class `w` in
`weilTrivialOnSpan F E N`. These are the classes spanned by continuous representations of
`W_E` on which `N` acts trivially. The approximate predicate asks for the relation after
raising both sides to some power `p^n`. Throughout, `E.field ≤ L.field` (`h`),
`weilInclusion F E L h : W_L → W_E` is the Library inclusion, and `E.unitsNorm L h` is the
Library norm `L^× → E^×`.

## Results

### Reciprocity and determinants

- `reciprocityUnits_weilInclusion F he E L h g`: for normalized reciprocity `e`,
  `reciprocityUnits F e E (weilInclusion F E L h g) = E.unitsNorm L h (reciprocityUnits F e L g)`.
  This is the norm square `NormRelation` of the coherent family, applied to the
  abelianization class of `g`.
- `fieldDeterminant_continuousRestrict F he E L h w γ`: the field determinant of the
  restriction of `w` to `W_L`, at `γ`, equals the field determinant of `w` at the norm of
  `γ`. The proof lifts `γ` to `W_L` and applies `ExactGrothendieckGroup.determinantCharacter_restrict`
  and the norm square.

### Test spans

- `restrictSubgroup F E L h N`, the named definition (an abbreviation), is
  `N.comap (weilInclusion F E L h)`: the subgroup `N ∩ W_L` of `W_L`.
- `continuousRestrict_mem_weilTrivialOnSpan F E L h N hw`: restriction to `W_L` sends
  `weilTrivialOnSpan F E N` into `weilTrivialOnSpan F L (restrictSubgroup F E L h N)`.
  A representation trivial on `N` restricts to one trivial on `N ∩ W_L`.
- `weilTrivialOnSpan_antitone F E hNN'`: if `N ≤ N'`, the span for `N'` lies in the span for
  `N`.
- `continuousRestrict_mem_degreeZero` and `continuousTensorSame_mem_degreeZero`: restriction
  preserves degree zero, and `w ⊗ x` has degree zero when `w` has. The second uses
  `degree_continuousTensor`.

### Monotonicity and additivity

- `exactWitnessOn_mono`, `approximateWitnessOn_mono`: a witness relative to `N` is a witness
  relative to any `N' ≥ N`, since there are fewer tests.
- `exactWitnessOn_zero`, `exactWitnessOn_add`, `exactWitnessOn_zsmul`: under the additive
  relation of `ε`, `1` is a witness for `0`. If `γ` and `γ'` are witnesses for `x` and `y`,
  then `γ γ'` is a witness for `x + y`, and `γ^n` is a witness for `n • x`.
- `approximateWitnessOn_zero`, `approximateWitnessOn_add`, `approximateWitnessOn_zsmul`: the
  same for the approximate relation. For a sum the exponent is `p^(n+m)`, from exponents
  `p^n` and `p^m`.

### The induction step

- `exactWitnessOn_induce hsys E L h N ψ x γ hx` assumes `IsSystem F e ε` and that `γ` is an
  exact witness for `x : Virtual F L`, relative to `restrictSubgroup F E L h N` and for
  the trace character `traceCharacter F E L h ψ`. It concludes that `E.unitsNorm L h γ` is an
  exact witness for `induce F E L h x`, relative to `N`.
  For a test `w` over `E`:
  - The projection formula `continuousTensorSame_induce` gives
    `w ⊗ Ind x = Ind (w|_{W_L} ⊗ x)`.
  - `w|_{W_L} ⊗ x` has degree zero, so the induction relation of `IsSystem` gives
    `ε_E(ψ)(Ind(w|_{W_L} ⊗ x)) = ε_L(ψ ∘ Tr)(w|_{W_L} ⊗ x)`.
  - `w|_{W_L}` is a test over `L` relative to `N ∩ W_L`, so the hypothesis gives
    `det(w|_{W_L})(γ)`.
  - This equals `det w (N_{L/E} γ)` by `fieldDeterminant_continuousRestrict`.
- `approximateWitnessOn_induce`: the same for the approximate relation, with the exponent of
  the hypothesis.

## Sources

Deligne–Henniart (1981), §4.5 (printed p. 110, PDF p. 22) and §4.8 (printed p. 111, PDF p. 23).
For `V = Σ n_i Ind_{L_i} χ_i` and a degree-zero test `W`, they write
`ε(W ⊗ V, ψ) = ∏ ε(W_i ⊗ χ_i, ψ ∘ Tr_{L_i/K})^{n_i}`, with `W_i` the restriction of `W` to
`W(K̄/L_i)`. They write `det W_i(a_i) = det W(N_{L_i/K}(a_i))` and conclude that
`∏ N_{L_i/K}(a_i)^{n_i}` is a witness. `exactWitnessOn_induce` is one factor of this
computation, in the relative-witness predicates. `exactWitnessOn_add` and
`exactWitnessOn_zsmul` assemble the product. The choice of the subgroups `N`, through the
break estimates of §4.8, is not part of this module.
