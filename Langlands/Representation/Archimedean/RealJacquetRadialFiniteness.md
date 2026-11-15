# Radial finiteness with bounded coefficients

Module: `Langlands.Representation.Archimedean.RealJacquetRadialFiniteness` (namespace
`Langlands.Archimedean.RealJacquetRadial`).

Main theorem: `Langlands.Archimedean.RealJacquetRadial.radial_finiteness`.

## Purpose and provenance

This is a helper module for the proof of
`Langlands.Archimedean.RealJacquetNonvanishingSubquotientReductionStatement`
(module `RealJacquetNonvanishingProof`). It supplies the radial-component step of Casselman's
matrix-coefficient argument for `V ≠ 𝔫V` (Wallach 1979, 4.13, which credits the argument to
Casselman and refers to Miličić for the asymptotics). The formulation for `GL_n(ℝ)` given here,
with the explicit letters `E_{ab} - r_{ab}² E_{ba}`, is internal to this formalization. The
proof reuses the word-reordering argument of the Library module
`RealJacquetFiniteGenerationProof` (the proof of `RealJacquetFiniteGenerationStatement`).

## Setting

- `Mat n` is the type of real `n × n` matrices, `E a b = Matrix.single a b 1`, and
  `op π X = π(1 ⊗ X)`. `wordOp π w` is the product of the `op π X` over a word `w`. `carry F S`,
  `boxSpace`, `diagEval`, `zdSpan` and `powerSumSpan` are the Library notions of
  `RealJacquetFiniteGenerationProof`.
- `Q` is a parameter type and `r : Q → Fin n → Fin n → ℝ`.
- `pointwise Q : End V →ₐ End (Q → V)` lets an endomorphism act pointwise, and
  `ptw Q π = (pointwise Q) ∘ π` is the pointwise Lie action on `Q → V`.
- `mulOp c` multiplies a function `Q → V` by `c : Q → ℂ`. `sq r a b = (q ↦ r q a b ²)`.
- `radLetter π r a b` acts at `q` by `op π (E a b - (r q a b)² • E b a)`: the radial letter
  `L_{ab}(r)`.
- `IsRadialStable π r S` says that for all `a < b` the subspace `S ⊆ (Q → V)` is stable under
  `radLetter π r a b`, under `mulOp (sq r a b)` and under multiplication by
  `q ↦ (1 - r q a b ²)⁻¹`.
- `constMap Q V : V →ₗ (Q → V)` sends `v` to the constant function `v`.

## Main result

`radial_finiteness`: assume `π` has an infinitesimal character, `r q a b ² ≠ 1` for all `q` and
all `a < b`, `F ⊆ V` is stable under `op π Y` for every antisymmetric `Y`, `S` is
`IsRadialStable π r S`, and `constMap Q V u ∈ S` for every `u ∈ boxSpace π F`. Then
`constMap Q V (wordOp π w f) ∈ S` for every word `w` and every `f ∈ F`.

For `r = 0` this is the statement `wordOp_mem_carry` behind `RealJacquetFiniteGenerationStatement`,
with the strictly upper triangular letters replaced by `L_{ab}(0) = E_{ab}`.

## Proof

The proof is the reordering argument of `RealJacquetFiniteGenerationProof`, run for the
pointwise action `ptw Q π` on `Q → V`, with `F' = F.map (constMap Q V)` in place of `F`.

**Pointwise action** (section `Pointwise`). `op (ptw Q π) X = pointwise Q (op π X)` and
`wordOp (ptw Q π) w = pointwise Q (wordOp π w)` (`op_ptw`, `wordOp_ptw`). The enveloping action
of `ptw Q π` is `pointwise Q` composed with that of `π` (`envelopingAction_ptw`, by
`UniversalEnvelopingAlgebra.lift_unique`), so `ptw Q π` has an infinitesimal character when `π`
does (`hasInfinitesimalCharacter_ptw`), and `diagEval (ptw Q π) = pointwise Q ∘ diagEval π`
(`diagEval_ptw`).

**Ring identities** (section `RingIdentities`): four identities in an arbitrary ring, proved by
`noncomm_ring` after rewriting with the given commutation hypotheses. They are stated
abstractly because `noncomm_ring` does not close the corresponding goals in `End (Q → V)`
directly.

**Letters** (section `Letters`). `radLetter_eq`: `L_{ab}(r) = op E_{ab} - mulOp(r²) op E_{ba}`.
Multiplication operators commute with all pointwise operators (`mulOp_mul_pointwise`).
`op_mul_radLetter` is the commutator `X L = L X + (op [X, E_{ab}] - mulOp(r²) op [X, E_{ba}])`.

**Reordering** (section `Carry`). For the strong induction on the word length `d`, assume that
every word of length `< d` carries `F'` into `S`.

- `radial_upper`: a word `u · L_{ab}(r) · v` with `|u| + |v| < d` carries `F'` into `S`. Move the
  letter `L_{ab}(r)` to the front one letter at a time (`carry_identity`). Each commutator term
  is a shorter word, possibly multiplied by `mulOp(r²)`, and `S` is stable under `L_{ab}(r)` and
  `mulOp(r²)`.
- `op_E_eq_radLetter_upper` / `_lower`: for `a < b`,
  `E_{ab} = (1 - r²)⁻¹ (L_{ab}(r) - r² (E_{ab} - E_{ba}))` and
  `E_{ba} = (1 - r²)⁻¹ (L_{ab}(r) - (E_{ab} - E_{ba}))` as operators on `Q → V` (with
  `r = r_{ab}`; `inv_mul_one_sub_sq` uses `r² ≠ 1`).
- `radial_offDiag`: a word of length `d` with an off-diagonal matrix unit carries `F'` into
  `S`. Rewrite the matrix unit by the previous item (`upper_identity`, `lower_identity`). The
  radial letter is handled by `radial_upper`. The antisymmetric letter `E_{ab} - E_{ba}` is
  handled by the Library lemma `wordOp_mem_carry_of_skew` (it moves to the end, where it
  preserves `F'`).
- `radial_zeroDiag`, `radial_diag_prefix`, `radial_zdSpan_le_carry`,
  `radial_diagEval_mem_carry`, `radial_diag_mem_carry`: as in the Library proof, words with a
  zero-diagonal letter reduce to the above. Words in the diagonal units `D_i` are monomials
  `h^γ` applied to `F'`. If all `γ_i < n` they lie in `boxSpace (ptw Q π) F' ⊆ S`. Otherwise
  the Library lemmas `monomial_mem_powerSumSpan` and `diagEval_psum` (the infinitesimal
  character applied to the Gelfand elements `tr(E^l)`) rewrite them through shorter words and
  zero-diagonal words.
- `radial_wordOp_mem_carry`: every word carries `F'` into `S`, by strong induction on the
  length.

**Constant functions** (section `Finiteness`). `F'` is stable under the antisymmetric letters
because `F` is. `boxSpace (ptw Q π) F' ≤ S`, because `diagEval (ptw Q π)` acts on constant
functions through `diagEval π` (`diagEval_ptw`) and each `diagEval π (monomial β 1) f`
(`f ∈ F`) lies in `boxSpace π F`. Applying `radial_wordOp_mem_carry` to the constant function
`f` and rewriting with `wordOp_ptw` gives `radial_finiteness`.
