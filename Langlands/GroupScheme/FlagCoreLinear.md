# Linear algebra of the flag covering core

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. It contains the
linear algebra of that core, stated for an abstract group `Γ` (in the application
the group of rational points of `G`) with a matrix representation
`ρ : Γ →* GL ι k` over a field `k`. The geometric inputs appear as hypotheses:
closed projective orbits, a diagonalized torus, and the Weyl-group step. They are
to be derived from the geometry in a separate module.

Everything is in the namespace `Langlands.GroupScheme.FlagCore`. Vectors are
functions `ι → k`. A linear form is a row vector `w`, acting by `w ⬝ᵥ v`. The
row action of a matrix is `w ᵥ* A`. The module imports
`Langlands.GroupScheme.FlagCoreLimit` (`weightPart`, `eval_weightPart_eq_zero`).

## Polynomial substitution

- `linearSubst M`: the `k`-algebra map `MvPolynomial σ k → MvPolynomial σ k`
  sending `X i` to `∑ l, M i l * X l`.
- `eval_linearSubst`: `eval x (linearSubst M f) = eval (M *ᵥ x) f`.
- `isHomogeneous_linearSubst`: `linearSubst M` preserves homogeneity of degree `d`.

## Closed orbits

- `IsClosedOrbit o`, for a family `o : Γ → σ → k`: every nonzero `c` on which
  every homogeneous polynomial vanishing at all `o g` also vanishes is of the form
  `a • o g` with `a ≠ 0`. This is the rational-point form of "the projective orbit
  of the lines `[o g]` is closed".
- `IsClosedOrbit.mulVec`: the property is preserved by `o g ↦ A *ᵥ o g` for an
  invertible matrix `A` with inverse `A'`. The proof pulls equations back with
  `linearSubst A'`.
- `IsClosedOrbit.smul`: preserved by `o g ↦ s g • o g` with every `s g ≠ 0`.
- `IsClosedOrbit.reindex`: preserved by reindexing coordinates along `τ ≃ σ`.
- `IsClosedOrbit.exists_weightPart` (contraction step), over an infinite field.
  Let `M` be a matrix with a left inverse `M'`, `dd : σ → ℤ` integer weights, and
  `c` an integer. Assume `c ≤ dd i` whenever `u i ≠ 0`, with equality for some
  `i` with `u i ≠ 0`. Assume also that for every `z ≠ 0` the vector
  `M *ᵥ (z ^ dd i * u i)_i` is a multiple of some `o g`. Then
  `M *ᵥ weightPart dd u c = a • o g` for some `g` and some `a ≠ 0`. The limit
  vector is nonzero because `M'` recovers `weightPart dd u c`, which is nonzero at
  the index of minimal weight. Each homogeneous equation of the orbit is moved by
  `linearSubst M` and then handled by `eval_weightPart_eq_zero`.

## Weights

Here `ι` and `I` are finite types. `wt : ι → I → ℤ` gives the weight of each
coordinate, `s : I → kˣ` is a torus point, and `d : ι → ℤ` is a vector of
integer levels.

- `exists_separating wt`: there is `ν : I → ℤ` such that
  `∑ a, ν a * wt i a = ∑ a, ν a * wt l a` implies `wt i = wt l`. The proof takes
  the product of the nonzero linear forms `∑ a, (wt i a - wt l a) X a` over the
  pairs with `wt i ≠ wt l`. This polynomial over `ℤ` is nonzero, so it does not
  vanish at some integer point `ν` (`MvPolynomial.funext`).
- `eq_of_forall_zpow_eq`: over an infinite field, if `z ^ m = z ^ m'` for all
  units `z`, then `m = m'`. Otherwise every nonzero `z` would be a root of
  `X ^ |m - m'| - 1`.
- `exists_min_level`: a nonzero vector `u` has a least level `c` among the
  indices `i` with `u i ≠ 0`, attained at one of them.
- `weightPart_ne_zero_level`: a nonzero coordinate of `weightPart d u c` has
  level `c`.
- `exists_of_dotProduct_weightPart_ne_zero`: if `x ⬝ᵥ weightPart d y c ≠ 0`,
  then some `i` has `x i ≠ 0`, `d i = c`, and `y i ≠ 0`.
- `dotProduct_weightPart_of_level`: if `x` is supported on level `c`, then
  `x ⬝ᵥ weightPart d y c = x ⬝ᵥ y`.
- `weightPart_dotProduct_weightPart`:
  `weightPart d x c ⬝ᵥ weightPart d y c = x ⬝ᵥ weightPart d y c`.
- `exists_weight_of_level`: if `d i = d l` implies `wt i = wt l`, then a vector
  supported on a single level is supported on a single weight `μ`.
- `charValue wt s i = ∏ a, s a ^ wt i a` (a unit), the value at `s` of the
  character of coordinate `i`.
- `diagonal_mulVec_of_weight`, `vecMul_diagonal_of_weight`: a vector supported on
  weight `μ` is an eigenvector of `diagonal (charValue wt s ·)` (acting on columns
  or on rows) with eigenvalue `∏ a, s a ^ μ a`.

## Tensors

- `kronecker_one_mulVec_tmul`: `(A ⊗ₖ 1) *ᵥ (x ⊗ y) = (A *ᵥ x) ⊗ y`, where
  `x ⊗ y` is the function `p ↦ x p.1 * y p.2` on `ι × ι`.
- `exists_smul_of_tmul_eq`: if `x, y ≠ 0` and `x ⊗ y = a • (x₂ ⊗ y₂)`, then `x₂`
  is a multiple of `x` and `y₂` is a multiple of `y`.

## Orbit vectors and the torus

Now `Γ` is a group, `ρ : Γ →* GL ι k`, and `τ : (I → kˣ) → Γ` is a family of
group elements (the torus points). `IsTorusFixed ρ τ u` means that every
`ρ (τ s)` maps `u` to a multiple of `u`. `IsTorusFixed.smul` says this property
passes to scalar multiples.

- Generalities: `exists_dotProduct_ne_zero` (if the vectors `o g` span the whole
  space, a nonzero row vector `r` has `r ⬝ᵥ o g ≠ 0` for some `g`).
  `mulVec_ne_zero` and `vecMul_ne_zero` (invertible matrices send nonzero vectors
  to nonzero vectors). `conj_mulVec` and `vecMul_conj` (how `P D P⁻¹` acts on
  `P *ᵥ u` and on `u ᵥ* P⁻¹`). `vecMul_inv_of_vecMul_eq`: if
  `w ᵥ* X = κ • w`, then `w ᵥ* X⁻¹ = κ⁻¹ • w`. `charValue_cochar`: if
  `d i = ∑ a, ν a * wt i a`, then the character of coordinate `i` takes the value
  `z ^ d i` at `(z ^ ν a)_a`.
- `orbitVec ρ e g = ρ g *ᵥ e`, `dualOrbitVec ρ w₀ g = w₀ ᵥ* ρ g⁻¹` (the
  transformed linear form), and
  `tensorOrbitVec ρ e w₀ g p = orbitVec ρ e g p.1 * dualOrbitVec ρ w₀ g p.2`.
- `orbitVec_mul`, `dualOrbitVec_mul`: how left multiplication by `x` acts on the
  two kinds of orbit vectors. `orbitVec_ne_zero`, `dualOrbitVec_ne_zero`.
  `dualOrbitVec_dotProduct_orbitVec`:
  `dualOrbitVec ρ w₀ g ⬝ᵥ orbitVec ρ e h = w₀ ⬝ᵥ orbitVec ρ e (g⁻¹ * h)`.
- `dualOrbitVec_eigen`: suppose every `h` that maps `e` to a multiple of `e`
  also maps `w₀` to a multiple of `w₀`. Then any `x` that maps `orbitVec ρ e g`
  to a multiple of itself maps `dualOrbitVec ρ w₀ g` to a multiple of itself.
  The proof applies the hypothesis to `g⁻¹ x g`.

In the rest of the section, `hτ` is the hypothesis
`ρ (τ s) = P * diagonal (charValue wt s ·) * P⁻¹` for all `s`, for a fixed
`P : GL ι k`.

- `isTorusFixed_of_level`: if `d` separates the weights and `u` is supported on
  one level, then `P *ᵥ u` is torus-fixed. `vecMul_torus_of_level`: under the same
  hypotheses, `u ᵥ* P⁻¹` is a row eigenvector of every `ρ (τ s)`, with a unit
  eigenvalue.
- `torus_curve_mulVec`, `torus_curve_vecMul`: with `d i = ∑ a, ν a * wt i a`,
  write `τ_z` for `τ ((z ^ ν a)_a)`. Then `ρ(τ_z)` maps `P *ᵥ u` to
  `P *ᵥ (z ^ d i * u i)_i`, and it maps a row vector `η` to
  `(z ^ d i * (η ᵥ* P) i)_i ᵥ* P⁻¹`.
- `level_eq_of_eigen`: over an infinite field, a row vector that is an
  eigenvector of every `diagonal (charValue wt s ·)` has all its nonzero
  coordinates on one `d`-level. The proof compares eigenvalues at `(z ^ ν a)_a`
  and applies `eq_of_forall_zpow_eq`.
- `IsTorusFixed.mulVec_of_normalizes`: if `m⁻¹ * τ s * m` is again a torus point
  for each `s`, then `ρ m` maps torus-fixed vectors to torus-fixed vectors.
- `exists_orbitVec_weightPart`: if the orbit of `e` is closed and
  `P *ᵥ u = orbitVec ρ e g`, then for a least level `c` of `u`,
  `P *ᵥ weightPart d u c` is a nonzero multiple of an orbit vector. This is
  `IsClosedOrbit.exists_weightPart` applied along the curve
  `z ↦ τ_z * g`.
- `isTorusFixed_of_eq_smul`: if `P *ᵥ weightPart d u c = a • v` with `a ≠ 0`
  and `d` separates the weights, then `v` is torus-fixed.
- `vecMul_diagonal_of_eigen`: if `ξ ᵥ* ρ (τ s) = c • ξ`, then
  `(ξ ᵥ* P) ᵥ* diagonal (charValue wt s ·) = c • (ξ ᵥ* P)`.

## Main theorem

`exists_semiInvariant_form` assumes the following, over an infinite field `k`:

- `e ≠ 0` and `w₀ ≠ 0`, and the vectors `orbitVec ρ e g` span `ι → k`;
- every `h` that maps `e` to a multiple of `e` maps the linear form `w₀` to a
  multiple of `w₀`;
- `IsClosedOrbit` holds for `orbitVec ρ e`, `dualOrbitVec ρ w₀`, and
  `tensorOrbitVec ρ e w₀`;
- `hτ` as above, for some `P`, `wt`, and `τ`;
- `hU`: each `x ∈ U` maps every torus-fixed orbit vector `orbitVec ρ e g` to a
  multiple of itself;
- `hweyl`: for any two torus-fixed orbit vectors `orbitVec ρ e g₁` and
  `orbitVec ρ e g₂` there is `m` such that `m⁻¹ * τ s * m` is a torus point for
  every `s`, and `orbitVec ρ e (m * g₂)` is a multiple of `orbitVec ρ e g₁`.

Then for every `g` there is a row vector `w` with `w ⬝ᵥ orbitVec ρ e g ≠ 0` and,
for each `x ∈ U`, a unit `c` with `w ᵥ* ρ x = c • w`.

The proof follows the numbered comments in the Lean source.

0. Choose a separating `ν` (`exists_separating`) and set
   `d i = ∑ a, ν a * wt i a`.
1. Write `orbitVec ρ e g = P *ᵥ v'`, let `cm` be the least level of `v'`, and
   contract (`exists_orbitVec_weightPart`): `P *ᵥ weightPart d v' cm` is a
   nonzero multiple of a torus-fixed `orbitVec ρ e g₁`.
2. Let `im` be an index of globally least level. By spanning, some
   `orbitVec ρ e gm = P *ᵥ um` has `um im ≠ 0`. Contracting it gives a
   torus-fixed `orbitVec ρ e g₂`, a nonzero multiple of
   `P *ᵥ weightPart d um (d im)`.
3. `hweyl` gives `m` relating `g₂` to `g₁`.
4. By spanning, `w₀ ⬝ᵥ orbitVec ρ e g₃ ≠ 0` for some `g₃`. The linear form
   `dualOrbitVec ρ w₀ (g₂ * g₃⁻¹)` pairs nonzero with `orbitVec ρ e g₂`. Hence
   `η' = dualOrbitVec ρ w₀ (g₂ * g₃⁻¹) ᵥ* P` pairs nonzero with
   `weightPart d um (d im)`.
5. Contract `η'` in the dual orbit along `z ↦ τ_z⁻¹ * (g₂ * g₃⁻¹)`, using the
   matrices `(P⁻¹)ᵀ` and `Pᵀ`. Because `d im` is the global minimum, the level
   bound holds automatically. The result `ξ₀ = weightPart d η' (d im) ᵥ* P⁻¹` is
   a nonzero multiple of a dual orbit vector `dualOrbitVec ρ w₀ h₀`. It is a
   torus row eigenvector, and it pairs nonzero with
   `P *ᵥ weightPart d um (d im)`.
6. Write `orbitVec ρ e h₀ = P *ᵥ u₀` with least level `c₀`. Contract the tensor
   orbit along `z ↦ τ_z * h₀`, using `P ⊗ₖ 1` and the levels `p ↦ d p.1`; along
   this curve the dual factor stays a multiple of `ξ₀`. This gives `g'` with
   `orbitVec ρ e g'` a multiple of `P *ᵥ weightPart d u₀ c₀`, which is
   torus-fixed, and `dualOrbitVec ρ w₀ g'` a nonzero multiple of `ξ₀`
   (`exists_smul_of_tmul_eq`).
7. Let `ξ = dualOrbitVec ρ w₀ (m * g')`. The vector `orbitVec ρ e (m * g')` is
   torus-fixed (`IsTorusFixed.mulVec_of_normalizes`). The pairing
   `ξ ⬝ᵥ orbitVec ρ e (m * g₂)` equals
   `dualOrbitVec ρ w₀ g' ⬝ᵥ orbitVec ρ e g₂`, which is nonzero by steps 2, 5
   and 6. Hence `ξ ⬝ᵥ P *ᵥ weightPart d v' cm ≠ 0`, by steps 1 and 3.
8. By `dualOrbitVec_eigen`, `ξ` is a row eigenvector of every `ρ (τ s)`. So
   `ξ ᵥ* P` lies on a single level (`level_eq_of_eigen`), and by step 7 this
   level is `cm`. Therefore
   `ξ ⬝ᵥ orbitVec ρ e g = (ξ ᵥ* P) ⬝ᵥ weightPart d v' cm ≠ 0`.
9. For `x ∈ U`, `hU` and `dualOrbitVec_eigen` make `ξ` an eigenvector of `ρ x`.
   The eigenvalue is nonzero because `ρ x` is invertible and `ξ ≠ 0`.

## Provenance

These are internal helper definitions and lemmas with no direct counterpart in the
literature. They are a linear-algebra replacement for part of the proof of Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 17.65
(printed pp. 374-375). There `G/B` is the orbit of a line `[v]` in `P(V)`. A
cocharacter of `T` with distinct weights contracts the orbit to an attracting
point `x₋`. A contraction in the contragredient `P(V^∨)` shows that the orbit of
the dual lowest-weight line `[v₋^∨]` is closed. The linear form `v₋^∨` then
cuts out an affine open subset stable under `I_u(T)`.

The route here is different. Weights need not be distinct: one separating
cocharacter `ν` is used, and limits are taken as lowest-weight parts
(`weightPart`). Closedness is used for three orbits, those of `e`, of `w₀`, and
of `e ⊗ w₀`. The Weyl-group step `hweyl` transports the resulting linear form so
that it does not vanish on the given orbit line. Milne's open cell (Proposition
13.52) is not used.
