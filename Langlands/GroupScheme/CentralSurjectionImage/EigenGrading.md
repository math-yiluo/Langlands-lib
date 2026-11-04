# Gradings of bialgebras by generalized eigenspaces of a right translation

Author: Worker 1387.

This internal, purely algebraic module lives in the namespace
`Langlands.GroupScheme.CentralSurjectionImage.EigenGrading`. Let `k : Type u` be a
field, `B` a commutative ring with a `Bialgebra k B` structure (cocommutativity
is not assumed), and `K` a field over `k`. Put `V k B K = K ⊗[k] B`. It is a
`K`-bialgebra by Mathlib's base-change instance.

## Right translation

For a `k`-algebra map `e : B → K` (a `K`-point):

- `extend e : V → K` is its `K`-linear extension, and `rho e : B → V` is the
  algebra map `b ↦ ∑ (1 ⊗ b₁) · e(b₂)` built from the comultiplication;
  `rtAlg e : V →ₐ[K] V` is the `K`-linear extension of `rho e`.
- `comul_one_tmul`: the comultiplication of `V` sends `1 ⊗ b` to the image
  `incl2 (comul b)` of the comultiplication of `B`.
- `rightAct_extend`: `rtAlg e` is the published right translation operator
  `AffineLinearEmbedding.rightAct (extend e)`; hence right translation is an
  algebra endomorphism. `rt e` is it as a `K`-linear endomorphism.
- `commute_rt_leftAct`: right translation commutes with every left translation
  `leftAct h` (published `rightAct_leftAct`), and `counit_leftAct` gives
  `counit (leftAct h v) = h v`.
- `rt_injective`: if `e' : B → K` is a left convolution inverse of `e`, that is
  `productMap e' e ∘ comul = algebraMap ∘ counit`, then `rt e` is injective,
  since `rightAct (extend e') ∘ rt e = rightAct counit = id`.
- `mul_mem_maxGenEigenspace`: for an algebra endomorphism, a product of
  generalized eigenvectors for `μ` and `ν` is a generalized eigenvector for
  `μν`. The proof is induction on the sum of nilpotency orders, using
  `(F - μν)(xy) = (F - μ)x · F y + μ · x · (F - ν) y`.

## The decomposition

Assume moreover `K` algebraically closed. `eig e μ` is the generalized
eigenspace of `rt e` for `μ`.

- `iSup_eig`: these span `V`. Every `v` lies in a finite-dimensional subspace
  stable under right translations, spanned by all its right translates
  (published `exists_fg_rightAct` and `rightAct_rightAct`). On it Mathlib's
  `iSup_maxGenEigenspace_eq_top` applies, and `genEigenspace_restrict` compares
  the eigenspaces.
- `isInternal_eig` and `decomposition`: with Mathlib's independence of
  generalized eigenspaces, `V` is their internal direct sum.
- `eig_zero`: with a left convolution inverse, `eig e 0 = ⊥`, by injectivity.
  `one_mem_eig`: `1 ∈ eig e 1`.
- `wt e μ` is the counit of the `μ`-component; `wt_of_mem` evaluates it on
  homogeneous elements.
- `conv_wt`: the functionals `wt e μ` are orthogonal convolution idempotents:
  `mul' (wt μ ⊗ wt ν) (comul v) = if μ = ν then wt μ v else 0`. On a homogeneous
  `v ∈ eig e ω` the left side is `wt ν (leftAct (wt μ) v)` (`mul'_map_comul`).
  Here `leftAct (wt μ) v` lies again in `eig e ω`, by commutation with right
  translation, and has counit `wt μ v`.

## The grading map

- `idx μ` is `Additive.ofMul (Units.mk0 μ _)` for `μ ≠ 0` (and `0` otherwise);
  `idx_mul`, `idx_one`.
- `gradeLin e` sends a homogeneous `w ∈ eig e ω` to `single (idx ω) (counit w)`
  in `K[Kˣ]` (`gradeLin_of_mem`). With a left convolution inverse,
  `coeff_gradeLin` computes its `u`-coefficient as `wt e u`, and `gradeLin_one`,
  `gradeLin_mul` make it a `K`-algebra map `gradeAlg`.
- `rt_one_tmul_grouplike`: for grouplike `g` (`comul g = g ⊗ g`), `1 ⊗ g` is an
  eigenvector of `rt e` with eigenvalue `e g`.

`exists_grading e e' he'` is the main result. Given a left convolution inverse
`e'` of `e`, there is a `k`-algebra map `ψ : B → K[Kˣ]` that is comultiplicative:
`mapDomain diagonal (ψ b) = productMap (inl ∘ ψ) (inr ∘ ψ) (comul b)`. It sends
every grouplike `g` with `counit g = 1` to the monomial of the unit `e g`. Here
`ψ` is `gradeAlg` restricted to `1 ⊗ B`. Comultiplicativity is `conv_wt`, read
through `coeff_gradeLin` and `coeff_productMap_inl_inr'` (from
`GroupAlgebraCoeff`).

## Provenance

This is an internal construction, and no literature result is attributed to
it. Right translation by a point is a locally finite algebra automorphism of
the coordinate ring. Its generalized eigenspaces grade the coordinate ring by
eigenvalues, and that grading is a homomorphism from a diagonalizable group. The
Lean proof uses no Jordan decomposition; it works directly with eigenspaces and
convolution idempotents.
