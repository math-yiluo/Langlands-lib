# Weyl words and the minimal-height argument (`WeylWords`)

Author: Worker 239.

Let `P : RootDatum J X Y` have a base `b`. This module writes Weyl group elements as words in
the simple reflections. It also proves the minimal-height argument that identifies a
Weyl-stable set of vectors with a set of roots.

## Weyl words

- `weylWord P b w`: for a list `w = [i₁, …, i_m]` of simple roots, the linear equivalence
  `s_{i₁} ∘ ⋯ ∘ s_{i_m}` of `X`. The lemmas `weylWord_nil`, `weylWord_cons`,
  `weylWord_cons_symm` and `weylWord_append_singleton` describe it.
- `exists_weylWord_root`: if `J` is finite and `P` is reduced, then every root `α_j` equals
  `weylWord P b w α_i` for some word `w` and some simple root `i`. The proof is the induction
  principle `RootPairing.Base.induction_reflect` of Mathlib. Simple roots are covered by the
  empty word, and reflecting by a simple root prepends a letter. For the negative of a root,
  append the letter `i` and use `s_i α_i = −α_i`.

## The minimal-height argument

- `coeff_eq_of_sum_eq`: integral coefficients with respect to the simple roots are unique,
  because the simple roots are linearly independent.
- `sum_ite_smul_root`: `Σ_t (k δ_{t,i}) α_t = k α_i`.
- `mem_range_root_of_weylStable` (for finite `J`): let `Λ ⊆ X` be a set such that
  1. `Λ` is stable under the simple reflections,
  2. every element of `Λ` is a nonnegative or nonpositive integral combination of the simple
     roots,
  3. `0 ∉ Λ`,
  4. `k • α_i ∈ Λ` for a simple root `α_i` implies `k = ±1`.

  Then every element of `Λ` is a root.

  Proof (private lemma `mem_range_root_of_weylStable_pos`, then a symmetric argument for the
  nonpositive case): strong induction on the height `N = Σ c_i` of `μ = Σ c_i α_i ∈ Λ`. Let
  `B = P.RootForm`. Since `μ ≠ 0` lies in the root span, `B(μ, μ) > 0` (Mathlib's
  `rootForm_pos_of_ne_zero`). Also `B(μ, μ) = Σ c_i B(μ, α_i)`, so some `i` has `c_i > 0`
  and `B(μ, α_i) > 0`. Hence `p = ⟨μ, α_i^∨⟩ > 0`, using `2 B(μ, α_i) = ⟨μ, α_i^∨⟩ B(α_i, α_i)`
  from `IntegralBase`. If `μ` is a multiple of `α_i`, then condition 4 gives `μ = α_i`.
  Otherwise some other coefficient of `μ` is positive. Then `s_i μ = μ − p α_i ∈ Λ` has
  coefficients `c − p δ_i`, so by condition 2 and uniqueness of coefficients it is a
  nonnegative combination of height `N − p < N`. By induction `s_i μ` is a root, and so is
  `μ = s_i (s_i μ)`.

## Provenance

Every root of a reduced root system is Weyl-conjugate to a simple root (Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §10.3, Theorem (c)); here this is
Mathlib's `Base.induction_reflect`. The minimal-height argument is the usual induction on the
height of a positive combination of simple roots, as in the proof that the positive roots are
reached from the simple roots by simple reflections. The statement for an abstract
Weyl-stable set `Λ` is internal to this project.
