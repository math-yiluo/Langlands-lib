# Irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-modules have an infinitesimal character

Lean module: `Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter`.

This module proves `Langlands.Archimedean.RealGKModuleInfinitesimalCharacterStatement` from
`Langlands.Representation.Archimedean.RealGenericLargeReduction`. The theorem is
`Langlands.Archimedean.InfinitesimalCharacter.realGKModuleInfinitesimalCharacter`. Its type is
exactly the statement, with no added hypotheses.

The statement says the following. Let `(ρ, π)` be an irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module in the sense of the Library (`IsRealGKModule`,
`IsIrreducibleGKModule`, `IsAdmissibleGKModule`). Then every element `z` of the center
`Z(𝔤)` of the universal enveloping algebra `U(𝔤)`, `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, acts on `V` by a
scalar.

The classical argument has two steps. The center commutes with `π(𝔤)` and with `ρ(K)`. Then
a Schur-type argument applies inside a finite-dimensional `K`-isotypic piece. The Lean proof
follows this outline. Its main work is the fact that conjugation by `k ∈ O(n)` fixes `Z(𝔤)`.
The proof uses no connectedness of `O(n)` and no Harish-Chandra isomorphism. Instead it shows
that conjugation by every invertible real matrix fixes `Z(𝔤)`, by the elementary argument
below.

## 1. Weight spaces (section `Weight`)

Let `B` be a complex algebra, `h ∈ B`, `σ` an algebra endomorphism of `B` and `c ∈ ℂ`,
`c ≠ 0`. For `m ∈ ℤ`, `weightSpace h σ c m` is the subspace of `a` with `h a - a h = m a` and
`σ a = c^m a`.

* `mul_mem_weightSpace`: the product of elements of weights `m` and `m'` has weight `m + m'`.
* `mul_mem_iSup_weightSpace`: so the sum of all weight spaces is closed under multiplication.
* `fixed_of_commute`: suppose `B` is the sum of the weight spaces, and `z` commutes with `h`.
  Then `σ z = z`. Proof: write `z = ∑ f_m` with `f_m` of weight `m`. Then
  `0 = [h, z] = ∑ m f_m`. The eigenspaces of the linear map `[h, ·]` are independent
  (`Module.End.eigenspaces_iSupIndep`), so `m f_m = 0` for all `m`. Hence `f_m = 0` for
  `m ≠ 0`, `z = f_0`, and `σ z = c^0 f_0 = z`.

## 2. The enveloping algebra (section `Enveloping`, `EnvMap`)

* `envInduction` is an induction principle for `U(L)`. A property that holds for scalars and
  for the generators `ι x`, and is stable under sums and products, holds for all of `U(L)`.
  Proof: such elements form a subalgebra `s`. The lift of the corestriction `L → s` composed
  with the inclusion `s → U(L)` is the identity, by the universal property.
* `mem_iSup_weightSpace_of_ι`: if every `ι x` lies in the sum of the weight spaces, so does
  every element of `U(L)`, by `envInduction` and step 1.
* `envMap φ` is the algebra endomorphism of `U(L)` induced by a Lie algebra endomorphism `φ`
  of `L`, namely `lift (ι ∘ φ)`. It is functorial (`envMap_comp`, `envMap_id`).
* `envMap_fixes_center`: let `e ∈ L` and `c ≠ 0`. Suppose `L` is the sum of the subspaces
  `lieWeight e φ c m = {y | [e, y] = m y, φ y = c^m y}`. Then `envMap φ` fixes every central
  `z`. Proof: with `h = ι e` and `σ = envMap φ`, every `ι y` lies in the sum of the weight
  spaces. By the previous item all of `U(L)` does, and `fixed_of_commute` applies.

## 3. Conjugation by an idempotent-type unit (section `Gl`)

* `lie_eq_mul_sub`: the Library's bracket on `ℂ ⊗_ℝ M_n(ℝ)` is the extension of scalars
  `LieAlgebra.ExtendScalars`. On pure tensors it is the commutator
  `[a ⊗ X, b ⊗ Y] = ab ⊗ (XY - YX)`, so it is the commutator of the algebra
  `ℂ ⊗_ℝ M_n(ℝ)`.
* `conjLie w` is conjugation `x ↦ w x w⁻¹` by a unit `w` of `ℂ ⊗_ℝ M_n(ℝ)`, a Lie algebra
  automorphism. It is built from the algebra map `unitConj w`.
* `envMap_conjLie_idempotent`: let `e` be an idempotent, `c ≠ 0` and `w = 1 + (c - 1) e`.
  Then `w⁻¹ = 1 + (c⁻¹ - 1) e` (`idempotent_unit_mul`), and `envMap (conjLie w)` fixes the
  center. Proof: every `x` is `exe + ex(1-e) + (1-e)xe + (1-e)x(1-e)`. These four pieces
  satisfy `[e, ·] = 0, 1, -1, 0` times the piece, and conjugation by `w` multiplies them by
  `1, c, c⁻¹, 1`. So `envMap_fixes_center` applies.

## 4. All invertible real matrices (section `Matrices`)

`FixesCenter M` says the following for a real matrix `M`: for every unit `w` of
`ℂ ⊗_ℝ M_n(ℝ)` with underlying element `1 ⊗ M`, `envMap (conjLie w)` fixes the center.

* `fixesCenter_one`, and `fixesCenter_mul`: if `M` is invertible and `M` and `N` have the
  property, so does `MN`. This uses `conjLie_mul` and `envMap_comp`.
* `fixesCenter_idempotent`: `1 + (c - 1) e` has the property for a real idempotent `e` and
  `c ≠ 0`, by step 3.
* `fixesCenter_diagonal`: an invertible diagonal matrix is the product of the matrices
  `diag(1, …, d_i, …, 1) = 1 + (d_i - 1) E_ii` (`diagonal_ite_eq`). The proof is induction on
  the set of indices.
* `fixesCenter_transvection`: for `i ≠ j`, the transvection `1 + c E_ij` equals
  `(1 - 2 E_jj)(1 - 2 Q)` with `Q = E_jj - (c/2) E_ij`. Both `E_jj` and `Q` are idempotents.
* `fixesCenter_of_det_ne_zero`: every invertible real matrix has the property. This uses
  Mathlib's induction principle `Matrix.diagonal_transvection_induction_of_det_ne_zero`
  (generation of `GL_n` by diagonal matrices and transvections).

## 5. Compatibility with `O(n)` (section `Compat`)

* `orthUnit k` is the unit `1 ⊗ k` for `k ∈ O(n)`. Its inverse is `1 ⊗ kᵀ`
  (`orthUnit_inv_val`). `det_ne_zero_of_orth` shows `det k ≠ 0`.
* `rho_mul_envelopingAction`: assume the last clause of `IsRealGKModule`,
  `ρ(k) π(1 ⊗ X) = π(1 ⊗ k X kᵀ) ρ(k)`. Then `ρ(k) π(u) = π(Ad(k) u) ρ(k)` for all `u ∈ U(𝔤)`,
  where `Ad(k) = envMap (conjLie (orthUnit k))`. Proof by `envInduction`. For generators
  `a ⊗ X = a • (1 ⊗ X)` this is the hypothesis and linearity.

## 6. Eigenvectors from admissibility (section `Eigen`)

`exists_eigenvector_of_commute` works for any group `K` with a topology. Let `ρ` be a
representation of `K` on `V` such that every vector is `K`-finite, every function
`k ↦ ℓ(ρ(k) v)` is continuous, and `ρ` is admissible in the Library's sense. Let `Z` commute
with every `ρ(k)` and let `v ≠ 0`. Then `Z` has an eigenvector. Proof:

* Let `W` be the span of the orbit of `v`. It is finite-dimensional and `K`-stable. Let `b`
  be a basis of `W` (`Module.finBasis`), and let `τ(k)` be the matrix of `ρ(k)` restricted to
  `W`. Then `τ` is a monoid homomorphism `K → M_d(ℂ)`. It is continuous: entry `(i, j)` is
  `ℓ(ρ(k) b_j)`, where `ℓ` is an extension of the `i`-th coordinate functional to `V`
  (`LinearMap.exists_extend`).
* The inclusion `T₀ : ℂ^d ≅ W ⊆ V` lies in `gkIntertwiners ρ d τ`
  (`LinearMap.toMatrix_mulVec_repr`), and `T₀ ≠ 0` because `v ∈ W`. By admissibility this
  space of intertwiners is finite-dimensional, and it is nonzero.
* `T ↦ Z ∘ T` maps intertwiners to intertwiners because `Z` commutes with `ρ`. Over `ℂ` it
  has an eigenvector `T ≠ 0` (`Module.End.exists_eigenvalue`): `Z ∘ T = c T`. Choose `x` with
  `T x ≠ 0`. Then `Z (T x) = c (T x)`.

## 7. The theorem

`realGKModuleInfinitesimalCharacter`: let `z` be central and `Z = envelopingAction π z`.

* `Z` commutes with every `π(X)`, because `z` commutes with `ι X` and `envelopingAction π` is
  an algebra map sending `ι X` to `π X`.
* `Z` commutes with every `ρ(k)`. By step 5, `ρ(k) Z = π(Ad(k) z) ρ(k)`, and `Ad(k) z = z` by
  step 4 applied to the invertible matrix `k`.
* `V ≠ 0` by irreducibility. Step 6 gives `c` and `x ≠ 0` with `Z x = c x`. The kernel `E` of
  `Z - c` is stable under `ρ` and `π`, since `Z` commutes with both, and `E ≠ 0`. So `E = V` by
  irreducibility, that is, `Z = c · id`.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Provenance

The fact proved is standard. Kostant (1978, p. 142) and Vogan (1978, p. 86) recall it for
irreducible Harish-Chandra modules. The usual proof uses connectedness of `GL_n(ℂ)` or the
Harish-Chandra isomorphism to see that `Ad(k)` fixes `Z(𝔤)`. The proof here (weight spaces of
idempotents, and generation of `GL_n(ℝ)` by diagonal matrices and transvections) is internal.
It was written for this formalization. The Schur-type step 6 is the usual argument for
admissible modules, adapted to the Library's admissibility condition, which is phrased with
spaces of `K`-intertwiners from matrix representations.
