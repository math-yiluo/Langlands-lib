# Standard Hecke scalars of invariantly paired spherical vectors

This module proves that the spherical spectra of two smooth representations of
`GL_(r+1)(F)` are inverse to each other when an invariant bilinear pairing
pairs their spherical eigenvectors nontrivially. Here `F : PadicField p` is the
published canonical p-adic field. The two representations `ρ` on `V` and `σ` on
`W` are arbitrary complex representations, in independent carrier universes,
that are smooth for the canonical group topology. The pairing
`B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` is assumed invariant: `B (ρ g x) (σ g y) = B x y`. The
module reuses the local instances and the Haar measure `sphericalHaar F r` of
`Langlands.Representation.Unramified.HeckeOperators`. That measure gives the
spherical subgroup `K = GL_(r+1)(O_F)` mass one.

Provenance: Henniart (2000), *A simple proof of the Langlands conjectures for
GL(n) over a p-adic field*, §2.2, states that association is preserved under
contragredients. Its indicated local input is that the Satake parameters of
`π^∨` are the inverses of those of `π`. This module proves that inversion
directly, as an internal derivation. It uses Hecke adjointness under an
invariant pairing and the inverse-transpose symmetry of `sphericalHaar`. It does
not use the Satake isomorphism or any identification of the smooth dual.

## Corner action, spherical projection and defects

- `corner F ρ hρ` abbreviates the published corner action
  `Hecke.cornerAction (sphericalHaar F r) ρ hρ K` of the spherical Hecke algebra on
  the `K`-fixed vectors.
- `functional_corner` writes every linear functional of a corner action as a
  scalar integral: `L (c ⋆ x) = ∫ c g * L (ρ g x)`. It unfolds the published
  corner and Hecke actions and applies `Hecke.integratedAction_dual`.
- `sphericalProjection F ρ hρ` abbreviates the published normalized averaging
  projection `Hecke.fixedProjection` onto the `K`-fixed vectors.
- `heckeDefect F ρ hρ c l` is the linear map `y ↦ (c - l) ⋆ e_K y` on the whole
  carrier, where `e_K` is the spherical projection. Its basic properties:
  - `heckeDefect_apply_fixed` evaluates it on a fixed vector, where the
    projection is the identity (`Hecke.fixedProjection_fixed`);
  - `corner_eq_smul_of_heckeDefect` recovers `c ⋆ x = l • x` from a vanishing
    defect at a fixed vector `x`;
  - `heckeDefect_eq_zero` proves that the defect vanishes identically when `c`
    acts by `l` on every fixed vector;
  - `heckeDefect_intertwiner` proves that every intertwiner `T : ρ → σ` commutes
    with the defects. It combines the published compatibilities
    `Hecke.fixedProjection_intertwiner` and `Hecke.cornerAction_intertwiner`.
- `pairing_sphericalProjection` proves `B (e_K y) w = B y w` for every `K`-fixed
  `w`. By `Hecke.integratedAction_dual`, the left side is the integral of the
  normalized indicator of `K` against `g ↦ B (ρ g y) w`. On `K` that function is
  the constant `B y w`, by invariance of `B` and `σ k w = w`. Therefore the
  integral is `μ(K)⁻¹ μ(K) B y w = B y w`, using `integral_indicator_const` and
  `Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero`.

## The central diagonal and the reversed double cosets

Write `t_j = standardDiagonal F r j`, the diagonal matrix with `j` uniformizers
followed by ones, and `n = r + 1`. Then `t_n` is the central uniformizer matrix.

- `standardDiagonal_last_commute` proves that `t_n` is central. Both products
  are diagonal-times-matrix products, with entries `ϖ * g i j` and `g i j * ϖ`.
- `last_mul_inv_standardDiagonal` proves `t_n t_j⁻¹ = w t_(n-j) w`. Here `w` is
  the permutation matrix `permGL Fin.revPerm` of the order reversal, and
  `n - j` is `j.rev`. The proof compares entries with
  `GeneralLinear.Cartan.permGL_mul_mul_apply`. On the diagonal it separates the
  cases `a < j` and `a ≥ j`.
- `mem_doubleCoset_rev_of_mem` proves that `x ∈ K t_j K` implies
  `t_n x⁻¹ ∈ K t_(n-j) K`. If `x = k₁ t_j k₂`, then
  `t_n x⁻¹ = (k₂⁻¹ w) t_(n-j) (w k₁⁻¹)`, because `t_n` is central and the
  previous identity holds. The permutation matrix `w` lies in `K` by
  `GeneralLinear.Cartan.permGL_mem`.
- `standardHeckeElement_inv` turns this into the identity of indicator functions
  `1_(K t_j K)(g⁻¹) = 1_(K t_(n-j) K)(t_n g)`. The converse inclusion is the same
  lemma applied to `t_n g`, together with `Fin.rev_rev`.
- `corner_last` proves that on a fixed vector `b`, the corner action of
  `1_(K t_n K)` is `σ t_n b`. Since `t_n` is central, `K t_n K = t_n K`. The
  published finite presentation formula
  `Hecke.integratedAction_eq_sum_of_presentation` with the single set `t_n K` of
  mass one (`measure_preimage_mul`, `sphericalHaar_self`) evaluates the integral.

## Adjointness of the standard Hecke scalars

`scalar_adjoint` assumes `K`-fixed vectors `a ∈ V` and `b ∈ W` that are
eigenvectors of all standard Hecke elements, with scalars `l i` and `l' i`, and
satisfy `B a b ≠ 0`. It concludes `l' j = l' n * l (n-j)`.

Proof. Let `c g = B (ρ g a) b`. It is bi-`K`-invariant, by invariance of `B` and
`K`-fixedness of `a` and `b`. By `corner_last`, `σ t_n b = l' n • b`. Hence
`c g = l' n * c (t_n g)`. By `functional_corner` and invariance of `B`,
`l' j * B a b = ∫ 1_(K t_j K)(g) c(g⁻¹) dg`. Substitute `g = θ u`, where `θ` is the
inverse transpose, which preserves `sphericalHaar`
(`sphericalHaar_measurePreserving_inverseTranspose`). By the published
`sphericalInverseTranspose_mem_doubleCoset_inv`, `θ u = k₁ u⁻¹ k₂` with
`k₁, k₂ ∈ K`. Bi-invariance then turns the integrand into
`1_(K t_j K)(u⁻¹) c(u)`. Next `standardHeckeElement_inv` and the central
relation give `l' n * 1_(K t_(n-j) K)(t_n u) c(t_n u)`. Left invariance of Haar
measure (`integral_mul_left_eq_self`) removes the translation by `t_n`. A
second application of `functional_corner` identifies the remaining integral with
`l (n-j) * B a b`. Cancelling `B a b ≠ 0` gives the claim.

## From adjoint scalars to inverse eigenvalues

The published `standardHeckeScalar F s i` is
`sqrt(q)^(i(n-i)) * elementaryCoefficient s i`, where `q` is the residue
cardinality. The polynomial lemmas are:

- `reverse_multiset_prod`: reversal of polynomials is multiplicative over a
  multiset (`Polynomial.reverse_mul_of_domain`);
- `reverse_one_sub_C_mul_X`: the reverse of `1 - z X` is `X - z` for a unit `z`;
- `eulerPolynomial_reverse`: the reverse of the published
  `Eigenvalues.eulerPolynomial s = ∏ (1 - z X)` is `∏ (X - z)`;
- `C_mul_eulerPolynomial_map_inv`: `(∏ (-z)) * ∏ (1 - z⁻¹ X) = ∏ (X - z)`, factor
  by factor.

`eq_map_inv_of_standardHeckeScalar` proves that spectra `s, s'` of rank `n` with
`λ'_j = λ'_n λ_(n-j)` for all `j` satisfy `s' = s.map (·⁻¹)`. Unfolding the
scalars, the powers of `sqrt(q)` on both sides agree, since `j(n-j)` is symmetric.
The sign factors are `(-1)^j` and `(-1)^n (-1)^(n-j)`. After cancelling the
nonzero powers of `sqrt(q)` and `-1`, the coefficients satisfy
`coeff P' j = c' * coeff P (n-j)`, where `P` and `P'` are the Euler polynomials
and `c'` is the leading coefficient of `P'`. Hence `P' = C c' * reverse P`. By
the previous lemma, `reverse P = C d * eulerPolynomial (s.map (·⁻¹))`, with
`d = ∏ (-z)`. Evaluation at `0` (`Eigenvalues.eulerPolynomial_eval_zero`) gives
`c' d = 1`. So `P'` is the Euler polynomial of `s.map (·⁻¹)`, and
`Eigenvalues.eulerPolynomial_injective` concludes.

`eq_map_inv_of_pairing` combines `scalar_adjoint` with this lemma. If
invariantly paired spherical vectors with `B a b ≠ 0` have the standard Hecke
scalars of `s` and of `s'`, then `s' = s.map (·⁻¹)`.
