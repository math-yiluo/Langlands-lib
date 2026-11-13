# Descending a Hermitian Galois cocycle to a special unitary group

Author: Worker 5375.

This internal module is the descent step of Task 6209
(`OuterTypeAHermitianPresentationStatement`). It builds an isomorphism from the special
unitary group scheme `SU(H)` of a Hermitian matrix onto a group `G` that becomes `SL_(n+1)`
over a Galois cover. The input is a local isomorphism whose Galois discrepancies have the
inner/outer shape of the published `SpecialLinearTitsCocycleStatement`. The module then
reads off the all-test matrix presentation of `G`.

## Setting

- `K`, `L`, `M` are fields in one universe `u`, with `IsScalarTower K L M`.
- `L/K` is separable quadratic (`Algebra.IsQuadraticExtension K L`,
  `Algebra.IsSeparable K L`), in any characteristic.
- `M/K` is assumed Galois (`IsGalois K M`) only for the descended isomorphism. No
  finiteness of `M/K` is used.
- `H : Form (fieldInvolution K L) (Fin (n + 1))` is a nonsingular Hermitian Gram matrix,
  and `GroupModel.groupScheme K L H` is its special unitary group scheme over `K`.
- `G` is a group scheme over `Spec K`, with an affine structure morphism for the
  descended isomorphism.
- `E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) K) G (cover K M)` is a
  local isomorphism from `SL_(n+1)` to `G` over `Spec M`.
- `coefficients`, `coverAut` and `discrepancy` are the published definitions of
  `SpecialLinearTitsCocycleStatement`.

## Coordinates at a cover point

For a cover point `a : Z ⟶ Spec M`, the following holds.

- `coefficients_algebraMap`: the coefficient map `M → Γ(Z)` is a `K`-algebra map.
- `fieldPoint L a : L →ₐ[K] Γ(Z)` is its restriction to `L`.
  - `fieldPoint_naturality` and `fieldPoint_coverAut` describe its behaviour under change
    of test scheme and under `coverAut K M σ`.
- `firstCoord L a` and `secondCoord L a` are the ring maps `L ⊗_K Γ(Z) → Γ(Z)` given by
  `ℓ ⊗ r ↦ φ(ℓ) r` and `ℓ ⊗ r ↦ φ(c ℓ) r`, where `φ = fieldPoint L a` and `c` is the
  conjugation of `L`. They come from `tensorProj` in `HermitianMatrixSplitting`.
- `secondCoord_eq`: the second map is the first one after the tensor conjugation.
- `coord_injective` and `coord_surjective`: together the two maps identify `L ⊗_K Γ(Z)`
  with `Γ(Z) × Γ(Z)`.
- `firstCoord_algebraMap` and `firstCoord_tensorMap` give the values on scalars from `L`
  and the naturality in the test scheme.
- `restrict_conjugation`: an automorphism `σ` of `M` that moves some element of `L`
  restricts to the conjugation of `L`. The proof combines Mathlib's `restrictNormal` with
  the published `conjugation_unique`.
- `firstCoord_coverAut_of_fixes` and `firstCoord_coverAut_of_moves`: translating the
  cover point by `σ` leaves the first map unchanged when `σ` fixes `L`. When `σ` moves
  `L`, it turns the first map into the second.

## Local isomorphisms

- `splitAt L H a` is `splitEquiv` from `HermitianMatrixSplitting`, for the extended form
  `SchemeModel.tensorForm K L H Z` and these two maps. It identifies the determinant-one
  isometries over `L ⊗_K Γ(Z)` with `SL_(n+1)(Γ(Z))`, and `coe_splitAt` states that it
  applies `firstCoord` to every entry.
- `localEquiv L H E a` composes four maps: the points equivalence of `SU(H)` from
  `HermitianMatrixGroupScheme`,
  `splitAt`, the inverse matrix model of `SL_(n+1)`, and `E.toFun a`.
  - `localEquiv_apply` unfolds it.
  - `localEquiv_naturality` gives naturality in the test scheme.
  - `localIso L H E` packages it as a `LocalGroupIso` from `SU(H)` to `G` over the cover.

## Discrepancy hypotheses

- `InnerTrivial L E`: every `σ : M ≃ₐ[K] M` fixing `L` pointwise has
  `discrepancy E σ a g = g` for every test scheme, cover point `a` and `g`.
- `OuterHermitian L H E`: every `σ` moving some element of `L` has discrepancy
  `X (g⁻¹)ᵀ X⁻¹`, on every test scheme and for every `a` and `g`. Here `X` is the
  coefficient image under `a` of `x = H⁻¹`, mapped from `L` to `M`. This is the outer
  clause of `SpecialLinearTitsCocycleStatement` with `x σ = H⁻¹`, in the same matrix
  shape, with `X` the image of `x σ`.

Under these hypotheses the following hold.

- `toFun_coverAut_of_discrepancy` converts a discrepancy identity into an equality of
  `E` at a cover point and at its Galois translate.
- `coefficients_gram_inv` and `coefficients_gram` identify the coefficient images of
  `H⁻¹` and `H` with the first coordinates of the extended Gram matrices.
- `localEquiv_coverAut`: the local isomorphisms are unchanged by `coverAut K M σ` for
  every `σ`.
  - If `σ` fixes `L`, the coordinates are unchanged and `InnerTrivial` applies.
  - If `σ` moves `L`, the coordinates are exchanged and `OuterHermitian` applies. The
    identity `splitSL_conj` from `HermitianMatrixSplitting`, `p(H⁻¹) (q(x)⁻¹)ᵀ p(H) = p(x)`, then gives the
    claim.
- `localIso_isInvariant` restates `localEquiv_coverAut` as the invariance hypothesis
  `LocalGroupIso.IsInvariant` of `Descent/LocalGaloisInvariant`.

## Descended isomorphism

- `descendedIso L H E hin hout : GroupModel.groupScheme K L H ≅ G` is
  `LocalGroupIso.galoisDescendIso` from `Descent/LocalGaloisInvariant`, applied to
  `localIso L H E`.
- `comp_descendedIso_hom`: for every test scheme `Z`, cover point `a` and point `y` of
  `SU(H)`, `y ≫ descendedIso.hom = localEquiv L H E a y`.

## Matrix presentation (section `Presentation`)

For any isomorphism `φ : GroupModel.groupScheme K L H ≅ G` with an arbitrary finite index
type, the following holds.

- `matrixPoints K L H φ T` is the group homomorphism from points of `G` over `T` to
  `GL(L ⊗_K Γ(T))`. It sends `x` to the tensor matrix of `x ≫ φ.inv`
  (`matrixPoints_apply`).
- `matrixPoints_injective`: it is injective on every test scheme.
- `mem_range_matrixPoints`: its image on every test scheme is exactly the set of `g` with
  `(ḡ)ᵀ (H ⊗ 1) g = H ⊗ 1` and `det g = 1`, where `ḡ` applies the tensor conjugation
  entrywise. The statement has the same shape as the corresponding clause of
  `OuterTypeAHermitianPresentationStatement`, with `J = H.gram`.
- `matrixPoints_naturality`: the matrix of `a ≫ x` is the matrix of `x` with `tensorMap a`
  applied entrywise.
- `matrixPoints_comp_hom` computes `matrixPoints` on points of the form `y ≫ φ.hom`.

## Provenance and scope

The provenance is internal. This is the classical description of an outer form of
`SL_(n+1)` as the special unitary group of a Hermitian form, by Galois descent of the
splitting `SU(H) ≅ SL_(n+1)` over a field containing `L`. Both discrepancy hypotheses
quantify over all test schemes and all cover points. The module does not produce `E` or
the Hermitian matrix: those come from the cocycle side of Task 6209. The torus clause is
in `OuterTypeAHermitianTorus`.
