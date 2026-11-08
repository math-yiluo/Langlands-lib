# Grading compact induction by an open normal subgroup

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

## Setting

- `G` is a topological group, `D` a commutative group with decidable equality, and `ν : G →* D` a
  homomorphism whose kernel is open.
- `P` is a subgroup with `P ≤ ker ν`, and `σ` is a complex representation of `P`.
- The induced representation is the Library's `Induction.compactInduced P σ`: right translation on
  smooth `σ`-covariant functions with compact support modulo `P`.

## Contents

- `gradedPiece hP hν d f`: the compactly induced function equal to `f` on `ν⁻¹(d)` and to `0`
  elsewhere (`eval_gradedPiece`).
  - It is linear (`gradedProjection`).
  - Translating shifts the degree: `gradedPiece_translate`,
    `gradedPiece d (R(s) f) = R(s) (gradedPiece (d · ν s) f)`.
  - It commutes with the action of `ker ν` (`gradedPiece_translate_ker`).
- `degreeSet ν f`, the image under `ν` of the support of `f`, is finite (`degreeSet_finite`).
  - The image of `P \ G` is compact, `ν` descends to a locally constant map on `P \ G`, and a
    locally constant map has finite image on a compact set.
  - `sum_gradedPiece`: `f` is the sum of its graded pieces over `degreeSet ν f`.
- Extension data:
  - `π` is a representation of `G` on `W`;
  - `f0 : c-Ind_P^G σ →ₗ W` intertwines the actions of `ker ν`;
  - `degreeComponent ν π f0 d w = π(t)⁻¹ f0(R(t) w)` for any `t` with `ν t = d`. It is
    independent of the choice of `t` (`degreeComponent_eq`), and `degreeComponent_translate`
    records its behaviour under translation.
- `twistedExtension ν π f0 hf0 hP hν χ`, for a character `χ : D →* ℂˣ`, is the intertwiner
  `c-Ind_P^G σ → (χ ∘ ν)⁻¹ ⊗ π` given by `z ↦ ∑_d χ(d) degreeComponent d (gradedPiece d z)`.
- `exists_twistedExtension_ne_zero`:
  - Hypotheses: the characters of `D` separate points, and `f0(R(t) gradedPiece (ν t) z) ≠ 0`.
  - Conclusion: some `twistedExtension χ z` is nonzero.
  - Proof: the evaluations `χ ↦ χ(d)` at distinct points `d` are distinct monoid homomorphisms
    from the character group to `ℂ`. They are linearly independent by Dedekind's theorem
    (Mathlib `linearIndependent_monoidHom`). Evaluating linear functionals on `W` then shows
    that every coefficient `degreeComponent d (gradedPiece d z)` vanishes, including the one
    at `d = ν t`.

## Provenance

These are elementary internal lemmas, not results quoted from a source. Their role is to extend
maps of representations of the open normal subgroup `M° = ker ν` of a product Levi `M` to maps of
representations of `M`, up to unramified twists. This is the reduction to `M°` in the theory of
cuspidal representations; Bernstein–Zelevinsky 1976, §3, treats `G°` in the same way.
