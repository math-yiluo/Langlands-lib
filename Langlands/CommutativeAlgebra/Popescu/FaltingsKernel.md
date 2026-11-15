# Kernels after base change, with a projective cokernel

This module provides a module-theoretic helper for Faltings' proof of Stacks, More on Algebra,
Proposition 15.36.1 (07E5), (2) ⇒ (4). The source says: "As `Ω_{A'/A}` is free (hence flat) we
get on tensoring with `K'` an exact sequence ... We conclude that the elements `da_j ⊗ 1` generate
`Ker(β)`." The lemma below is the precise statement used for that step. It lives in
`Langlands.CommutativeAlgebra.Popescu.Faltings`.

## `ker_lTensor_eq_range`

Let `R` be a commutative ring, `M → N → P → 0` an exact sequence of `R`-modules (`φ`, then a
surjective `ψ`) with `P` projective, and `Q` any `R`-module. Then

`ker(Q ⊗ φ) = image(Q ⊗ ker φ → Q ⊗ M)`.

Proof:
1. `P` is projective, so `ψ` has a section `s` (`Module.projective_lifting_property`). Then
   `x ↦ x − s(ψ x)` is a retraction `N → range φ` of the inclusion `range φ ⊆ N`.
2. Consequently `Q ⊗ range φ → Q ⊗ N` is injective, because it has a left inverse.
3. `Q ⊗ φ` factors as `Q ⊗ M → Q ⊗ range φ → Q ⊗ N`. So its kernel is the kernel of
   `Q ⊗ M → Q ⊗ range φ`.
4. By right exactness of `Q ⊗ −` (`lTensor_exact`) applied to
   `0 → ker φ → M → range φ → 0`, that kernel is the image of `Q ⊗ ker φ`.
5. The reverse inclusion holds because `φ` vanishes on `ker φ`.
