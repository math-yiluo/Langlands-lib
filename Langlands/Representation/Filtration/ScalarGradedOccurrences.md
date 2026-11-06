# A character met by a subrepresentation and by its quotient occurs in two grades

Author: Worker 1714. This is an internal auxiliary lemma for the proof of Renard VII.1.3.
It is linear algebra about finite filtrations; no representation theory of `p`-adic groups
is used.

## The statement

`TwoScalarGradesStatement` is about a natural finite filtration
`s : RepFunctorFiltration F n` of a functor `F : C ⥤ Rep k G`, where `k` is a field and
`G` a monoid. It is used at one object `X`. Fix the following data:

- representations `R i` with isomorphisms `e i : (s.graded i).obj X ≅ R i`;
- a family of elements `ι : B → G`;
- scalars `c : Fin n → B → k`.

Assume `ScalarGraded.ZeroOrScalarIrreducible R ι c`: every `R i` is zero, or it is
irreducible (`Representation.IsIrreducible`) and each `ι t` acts on it by the scalar
`c i t`. Let `E` be a subrepresentation of `(F.obj X).ρ` and `χ : B → k`. Suppose that
there are

- a nonzero `v ∈ E` with `((ρ (ι t) - χ t)^d) v = 0` for all `t`, and
- a vector `w ∉ E` with `((ρ (ι t) - χ t)^d') w ∈ E` for all `t`.

Then there are two distinct indices `i ≠ j` with `R i` and `R j` nonzero and
`c i = c j = χ`. `twoScalarGrades` proves the statement.

In the intended use, `X` is the representation `ρ` of the Levi factor and `F` is
`r_Q ∘ i_P`, with the filtration of the geometric lemma. `E` is the image of the Jacquet
module of a subrepresentation `π₁ ⊆ i_P ρ`, and `w` lifts a vector of the Jacquet module of
the quotient `π₂`. The elements `ι t` are the points of a split component, and `χ` is a
common exponent of `π₁` and `π₂` along `Q`.

## The proof

1. `ScalarGraded.exists_step`: a chain of propositions that is false at the start and true
   at the end switches from false to true at some step.
2. `ScalarGraded.pow_sub_smul_apply_sub_mem`: if `f` preserves `T` and acts on `T` by `c`
   modulo `S`, then `(f - b)^m` acts on `T` by `(c - b)^m` modulo `S`.
3. Lemma A, `ScalarGraded.exists_grade_of_pow_apply_eq_zero`. By step 1 there is an
   index `i` with `v` in the upper step `F i.succ` but not in the lower step
   `F i.castSucc`. If `c i t ≠ χ t`, then by step 2, `(c i t - χ t)^d v` lies in the lower
   step. As `(c i t - χ t)^d` is invertible, so does `v`, a contradiction.
4. Lemma B, `ScalarGraded.exists_grade_of_pow_apply_mem`. This is the same argument with
   the steps enlarged by `E`. It gives an index `j` with `c j = χ`, and a vector `u` of the
   upper step outside `F j.castSucc ⊔ E`.
5. Lemma C, `ScalarGraded.exists_two_grades`. This is stated for steps that are
   subrepresentations with no subrepresentation strictly between consecutive steps. If
   lemmas A and B gave the same index `i`, consider
   `F i.castSucc ⊔ (E ⊓ F i.succ)`. It lies between the two steps, so it equals one of
   them. If it is the lower step, `v` lies there, contradicting lemma A. If it is the
   upper step, `u` lies in `F i.castSucc ⊔ E`, contradicting lemma B.
6. Section `Quotient` passes from a graded piece to vectors.
   `apply_sub_smul_mem_of_intertwiningMap` uses an intertwining map `π` from `T` to `σ`
   with kernel `S`: if `g` acts on `σ` by `c`, then `ρ g x - c • x ∈ S` for `x ∈ T`.
   `eq_or_eq_of_intertwiningMap` uses such a map to a zero or irreducible `σ`: then no
   subrepresentation lies strictly between `S` and `T`. The image of such a
   subrepresentation is `⊥` or `⊤`.
7. Namespace `RepFunctorFiltration` applies this to
   `gradedModelProjection s X i e`, the quotient projection of the `i.succ`-th step followed
   by `e i`. Its kernel is the `i.castSucc`-th step
   (`gradedModelProjection_eq_zero_iff`). A vector of the upper step outside the lower one,
   or distinct consecutive steps, make `R i` nonzero (`nontrivial_of_mem_of_notMem`,
   `nontrivial_of_ne`). A zero piece satisfies the scalar condition trivially, so every
   grade does. `exists_grade_of_pow_apply_eq_zero`, `exists_grade_of_pow_apply_mem` and
   `exists_two_grades` are lemmas A, B and C for the filtration. Each concludes that the
   grades it finds are nonzero.

## Provenance

The statement is internal. It has no separate counterpart in the literature. It serves
the comparison of the two constituents `0 → π₁ → π → π₂ → 0` of `π = i_P ρ` in the proof
of Renard VII.1.3 (printed p.225). There, `r_P π = ρ` is irreducible, so by exactness
`r_P π₁` and `r_P π₂` cannot both be nonzero. The lemma here is a variant at the level of
graded pieces: one nonzero irreducible graded piece of `r_Q π` cannot supply an exponent
to both `r_Q π₁` and `r_Q π₂`. The Lean proof works with vectors and generalized
eigenvectors. It needs neither Jordan–Hölder theory nor finite length.

## Scope

- `k` is any field and `G` any monoid; `C` is any category.
- The filtration may have zero graded pieces and repeated steps.
- No finiteness or admissibility is assumed. The exponents `d` and `d'` are independent.
