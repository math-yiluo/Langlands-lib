# Bialgebra maps to group algebras that are isomorphisms modulo a small ideal

This module is an internal helper for part (2) of
`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalDeformationStatement`. Its route is our
own: instead of the infinitesimal argument in Conrad's notes (Appendix B, B.3.2), it uses the
grading of a bialgebra coacting through a map to a group algebra (published module
`Langlands.Algebra.GroupAlgebraCoaction`, with `proj`, `grade`, `coeffForm`) and Nakayama's
lemma.

## Setting

`K` is a commutative ring, `N` an additive commutative group, `A` a commutative `K`-bialgebra,
and `π : A →ₐc[K] K[N]` a bialgebra map.

## Statements

- `map_mem_smul_top f I hx`: a linear map sends `I • ⊤` into `I • ⊤`.
- `form_mem_of_mem_smul_top f I hx`: a linear form sends `I • ⊤` into `I`.
- `apply_of_mem_grade π hb`: if `b ∈ grade π n` then `π b = single n (counit b)`.
- `proj_mem_ker π ha m`: if `π a = 0` then `π (proj π m a) = 0`.
- `exists_mem_grade_apply_eq_single π hsurj n`: if every degree `n` has some `a` with
  `(π a).coeff n` a unit, then every degree has `y ∈ grade π n` with `π y = single n 1`.
- `surjective_and_ker_eq_span_idempotent π I hI hsurj hinj`: assume `A` is noetherian,
  `I ≤ jacobson ⊥` in `K`, every degree `n` has an `a` with `(π a).coeff n` a unit, and
  `π a ∈ I • ⊤` implies `a ∈ I • ⊤` for every `a`. Then `π` is surjective and there is an
  idempotent `e : A` with `ker π = Ideal.span {e}`.

Geometrically, the last statement says that `Spec π : D(N) → Spec A` is a closed immersion
whose image is also open; that translation is not part of this module.

## Proof of the main statement

Choose homogeneous `y n ∈ grade π n` with `π (y n) = xⁿ`; they define a linear section `s` of
`π`, so `π` is surjective and `P = id - s ∘ π` is a linear projection onto `ker π`. If
`k ∈ ker π`, the injectivity hypothesis gives `k ∈ I • ⊤`, and applying `P` gives
`k ∈ (I A) • ker π`. Since `ker π` is finitely generated (noetherian `A`), Nakayama's lemma
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) gives `r` with
`r - 1 ∈ I A` and `r • ker π = 0`. The kernel is stable under the homogeneous projections, and
`proj π 0` is linear over the degree-zero part, so `r₀ = proj π 0 r` also kills `ker π`. Its
counit is `≡ 1` modulo `I`, hence a unit, so `r' = counit(r₀)⁻¹ r₀` satisfies `π r' = 1` and
`r' • ker π = 0`. Then `r' - 1 ∈ ker π` gives `r'² = r'`, and `e = 1 - r'` is an idempotent
generating `ker π`.
