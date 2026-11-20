# `Lie P = Lie U ⊕ Lie Z` and the Levi restriction of `det Ad_P`

Author: Worker 759.

Module `Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition` is a helper module for the
proof of `Langlands.Global.AdelicGroupPoints.AdelicParabolicModulusStatement` (module
`Langlands.Global.AdelicParabolicModulusProof`). It contains no proposition definitions; all its
declarations are definitions of maps and proved theorems.

Throughout, `χ` is a cocharacter of a group scheme `G` and `iP : P ⟶ G`, `iZ : Z ⟶ G`,
`iU : U ⟶ G` represent the dynamic subgroups `P(χ)` (`Dynamic.parabolic χ`), `Z(χ)`
(`Dynamic.centralizer χ`, the Levi factor) and `U(χ)` (`Dynamic.unipotent χ`). The maps
`unipotentToParabolic hP hU : U ⟶ P` and `centralizerToParabolic hP hZ : Z ⟶ P` are the
published inclusions.

## Provenance

The content is internal and derived. Its only geometric input is the published Levi
decomposition on points, `Dynamic.semidirectEquiv χ T : U(χ)(T) ⋊ Z(χ)(T) ≃* P(χ)(T)`
(module `Langlands.GroupScheme.Dynamic.LimitMap`, the points form of Conrad's Theorem 4.1.7(3)
used in `Langlands.GroupScheme.Dynamic.SchemeDecomposition`). It applies this on dual-number
points to obtain the Lie-algebra decomposition `Lie P = Lie U ⊕ Lie Z`. The determinant
identity is then the linear-algebra fact that a block-diagonal endomorphism of a product of two
finite free modules has determinant the product of the two block determinants
(`LinearMap.det_prodMap` in Mathlib). These are standard facts and no literature passage is
formalized here.

## Points (arbitrary base scheme `S`, `G` separated)

- `eq_one_of_unipotent_mul_centralizer_eq_one`: if `u ∈ U(χ)(T)`, `z ∈ Z(χ)(T)` and `u z = 1`,
  then `u = 1` and `z = 1`. Proof: `semidirectEquiv χ T` is injective and sends `(u, z)` to `u z`.
- `exists_eq_unipotent_mul_centralizer`: every `T`-point `p` of `P` is
  `(u ≫ U ⟶ P) * (z ≫ Z ⟶ P)` for some `T`-points `u` of `U` and `z` of `Z`. Proof: decompose
  the image of `p` in `G(T)` with `(semidirectEquiv χ T).symm`, lift both factors through the
  representing inclusions, and cancel the monomorphism `iP`.
- `limitGroupHom_eq_one_iff`: a `T`-point `p` of `P` is killed by the published limit
  homomorphism `limitGroupHom hP hZ : P ⟶ Z` if and only if its image in `G(T)` is a point of
  `U(χ)`. Proof: `limitGroupHom_comp` identifies the image in `G` of `p ≫ limitGroupHom` with
  the limit `lim_{t → 0} χ(t) p χ(t)⁻¹`, and the published `limit_eq_one_iff` characterizes
  `U(χ)` by trivial limit.

## Lie algebras (affine base `Spec R`, all three representatives affine morphisms)

For an `R`-algebra `A`, `lieKernel H A` is the published kernel of `H(A[ε]) → H(A)`, an
`A`-module under the epsilon scaling.

- `lieProductMap hP hZ hU A : Lie U × Lie Z →ₗ[A] Lie P` is `(x, y) ↦ x + y`, where `x` and `y`
  are mapped into `Lie P` by `Lie.targetMapLinear` along `U ⟶ P` and `Z ⟶ P`.
  `lieProductMap_val_comp` states that after `iP` the value is the product
  `(x ≫ iU) * (y ≫ iZ)` in `G(A[ε])`.
- `lieProductMap_injective`: if the sum vanishes then `(x ≫ iU) * (y ≫ iZ) = 1`, so both
  factors are `1` by `eq_one_of_unipotent_mul_centralizer_eq_one`, and `x = y = 0` because
  `iU` and `iZ` are monomorphisms.
- `lieProductMap_surjective`: for `w ∈ Lie P`, decompose its image in `G(A[ε])` as `u z` with
  `semidirectEquiv`. Reducing along `A[ε] → A` gives `u₀ z₀ = 1` in `G(A)`, so `u₀ = z₀ = 1`.
  Hence the lifts of `u` and `z` to `U` and `Z` lie in the Lie kernels, and their sum is `w`.
- `lieProductEquiv hP hZ hU A` is the resulting linear isomorphism
  `Lie U × Lie Z ≃ₗ[A] Lie P`.
- `differential_lieProductMap`: for a point `z` of `Z` over `A`, the differential of
  conjugation by the image of `z` in `P` (`(AutomorphicAction.conjugation (𝟙 P)).differential`)
  sends `x + y` to `x' + y'`. Here `x'` is the image of `x` under the published action
  `centralizerAdjointAction hZ hU` of `Z` on `U` (`u ↦ z u z⁻¹`), and `y'` the image of `y`
  under the adjoint action of `Z` on itself. The proof is a computation in the group
  `G(A[ε])` after the monomorphism `iP`, using `centralizerAdjointAction_act_comp`.
- `det_conjugation_centralizerToParabolic`: if `Lie U` and `Lie Z` are finite free over `A`,
  then `det(Ad_P(z) | Lie P) = det(Ad(z) | Lie U) · det(Ad_Z(z) | Lie Z)`. The conjugation on
  `Lie P` is the conjugate by `lieProductEquiv` of `LinearEquiv.prodCongr` of the two blocks.
  Apply `LinearEquiv.det_conj` and `LinearMap.det_prodMap`.

## Rational characters (base a field `k`)

`characterRestrict_adjointDeterminantCharacter_parabolic`: let `P` and `Z` be affine and
locally of finite type, `U` affine, and let `c : Lie.FiniteCoordinates U d` be any finite
coordinates. Then

```
characterRestrict (centralizerToParabolic hP hZ) (Lie.adjointDeterminantCharacter P) =
  (centralizerAdjointAction hZ hU).determinantCharacter c + Lie.adjointDeterminantCharacter Z.
```

So the restriction to `Z` of `det(Ad | Lie P)` is `det(Ad | Lie U)` (computed in the
coordinates `c`) plus `det(Ad | Lie Z)`, as characters of `Z`. The proof uses the published
`rationalCharacters_ext_affinePoints` (characters of an affine group are determined by their
values on points over all `k`-algebras). On a point `z` over `A`, the three characters
evaluate to the corresponding determinants of differentials
(`Lie.adjointDeterminantCharacter_affinePoints`,
`AutomorphicAction.determinantCharacter_affinePoints`). A sum of characters evaluates to the
product of the values (`rationalCharacters.comp_add`). The identity of
`det_conjugation_centralizerToParabolic` then gives the result. Finite freeness of `Lie U` and
`Lie Z` over `A` comes from the coordinates `c` and from the published
`Lie.finiteCoordinates Z`.

No reductivity is assumed in this module. In the main proof, `Lie.adjointDeterminantCharacter Z`
is shown to vanish because `Z` is connected reductive.
