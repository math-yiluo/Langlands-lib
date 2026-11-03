# Finite linear models of kernels between finite projective modules

This module provides a pure-algebra helper for the noetherian finite linear model
of line-bundle Hom (`LineHom.NoetherianModelStatement`). It extends the Library's
finite free result `FiniteLinearEquations.TensorKernel.kernelEquiv` from finite
free modules to finite projective modules.

## Main theorem

`exists_kernel_solutions_model` takes a commutative ring `R` and an `R`-linear
map `f : P → Q` between finite projective `R`-modules in the same universe. It
produces natural numbers `m, n`, an `m × n` matrix `a` over `R`, and, for every
commutative `R`-algebra `S` in that universe, a bijection `E S` between:

- the kernel of `1_S ⊗ f : S ⊗_R P → S ⊗_R Q`, and
- `Solutions a S`, the vectors `x : Fin n → S` with
  `∑ i, a j i * x i = 0` for every row `j`.

These bijections are natural in `S`. For every `R`-algebra map `q : S → S'` and
every kernel element `z`, mapping `z` with `q ⊗ 1_P`
(`TensorKernel.mapKernel f q.toLinearMap`) and then applying `E S'` gives the
same result as applying `q` coordinatewise to `E S z` (`mapSolutions a q`). The
theorem does not assert that `P` or `Q` is free, and it puts no noetherian
hypothesis on `R`.

## Auxiliary declarations

- `exists_retract_fin`: a finite projective module `P` is a retract of some
  `Fin n → R`. There are linear maps `i : P → R^n` and `π : R^n → P` with
  `π ∘ i = id`. Choose a surjection `R^n → P` (`Module.Finite.exists_fin'`) and
  lift the identity of `P` along it (`Module.projective_lifting_property`).
- `prodCoordinates n₁ n₀`: the linear equivalence
  `(Fin n₁ → R) × (Fin n₀ → R) ≃ (Fin (n₁ + n₀) → R)`, built from
  `LinearEquiv.sumArrowLequivProdArrow` and `finSumFinEquiv`.
- `replacement f i₀ π₀ i₁ : F₀ → F₁ × F₀` is the map
  `x ↦ (i₁ (f (π₀ x)), x - i₀ (π₀ x))`. Here `i₀ : P → F₀`, `π₀ : F₀ → P`
  and `i₁ : Q → F₁` are linear maps.
- `lTensor_retract`: if `π₀ ∘ i₀ = id`, then `(1 ⊗ π₀) ∘ (1 ⊗ i₀) = id` after
  tensoring with any module `A`.
- `lTensor_replacement_eq_zero_iff`: suppose `π₁ ∘ i₁ = id` for some
  `π₁ : F₁ → Q`. Then for any module `A` and any `z ∈ A ⊗ F₀`,
  `(1 ⊗ replacement) z = 0` holds exactly when both of these hold:
  `(1 ⊗ f)((1 ⊗ π₀) z) = 0` and `(1 ⊗ i₀)((1 ⊗ π₀) z) = z`.
- `replacementKernelEquiv f h₀ h₁ A`: assuming `π₀ ∘ i₀ = id` and
  `π₁ ∘ i₁ = id`, the bijection between `ker(1_A ⊗ replacement)` and
  `ker(1_A ⊗ f)`. It sends `z` to `(1 ⊗ π₀) z`, and its inverse is `1 ⊗ i₀`.
- `replacementKernelEquiv_symm_mapKernel`: the inverse of this bijection
  commutes with `mapKernel` along any coefficient map `q : A → B`. Both
  composites equal `q ⊗ i₀`.

## Proof

Take retractions `(i₀, π₀)` of `P` onto `R^{n₀}` and `(i₁, π₁)` of `Q` onto
`R^{n₁}`. Then `f' := replacement f i₀ π₀ i₁` is a map from `R^{n₀}` to
`R^{n₁} × R^{n₀}`. Apply `1_S ⊗ -` to its two components. The first becomes
`(1 ⊗ i₁)(1 ⊗ f)(1 ⊗ π₀)`, and `1 ⊗ i₁` is injective because `1 ⊗ π₁` is a left
inverse. The second becomes `1 - (1 ⊗ i₀)(1 ⊗ π₀)`. So
`ker(1_S ⊗ f') ≃ ker(1_S ⊗ f)` through `1 ⊗ π₀` and `1 ⊗ i₀`, as in
`lTensor_replacement_eq_zero_iff` and `replacementKernelEquiv`.

The model matrix is `a := TensorKernel.matrix f' (refl) (prodCoordinates n₁ n₀)`,
with `m = n₁ + n₀` and `n = n₀`. The bijection is
`E S := (replacementKernelEquiv f h₀ h₁ S).symm.trans
(TensorKernel.kernelEquiv f' (refl) (prodCoordinates n₁ n₀) S)`. Naturality
follows from `replacementKernelEquiv_symm_mapKernel` and the Library lemma
`TensorKernel.kernelEquiv_naturality`.

## Provenance

This is an internal helper, requested by the Hom-proof task
(b792240c-c046-4cc7-9705-872daf853dd0) with exactly this statement for
`exists_kernel_solutions_model`. Its content is standard commutative algebra: a
finitely generated projective module is a direct summand of a finite free module,
and kernels of maps between such modules, after any base change, are cut out by
finitely many linear equations. The replacement map is the usual
split-idempotent trick, which avoids needing `P` or `Q` to be free. No external
source is formalized beyond this.
