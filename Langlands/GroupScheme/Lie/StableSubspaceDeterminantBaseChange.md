# Determinant characters on stable subspaces under field extension

Let `K/k` be a field extension, `b = algebraBaseMap k K`, and let `G_K`, `M_K`
and `l_K` be the base changes along `b` of `G`, `M` and `l : M ⟶ G` (with `G`
affine and locally of finite type over `Spec k`). Let `V ⊆ Lie(G)(k)` and
`V_K ⊆ Lie(G_K)(K)` be subspaces with bases `bV` and `bK` on the same index
type that are matched by the scalar extension of Lie algebras:

```
hb : ∀ j, (bK j : Lie(G_K)(K)) = schemeScalarExtension G (1 ⊗ bV j).
```

Here `Lie.schemeScalarExtension G : K ⊗[k] Lie(G)(k) ≃ Lie(G_K)(K)` is the
Library's comparison (module `Langlands.GroupScheme.Torus.WeightBaseChange`).
This module shows that stability of `V` passes to `V_K`, and that the
determinant character of the module
`Langlands.GroupScheme.Lie.StableSubspaceDeterminant` commutes with base
change. The declarations are in the namespace `Langlands.GroupScheme.Lie`.

## The comparison of scalar extensions

For a `K`-algebra `B` that is also a `k`-algebra (with
`IsScalarTower k K B`), `extensionComparison bV bK B : B ⊗[K] V_K ≃ₗ[B]
B ⊗[k] V` is the linear equivalence `Module.Basis.equiv` that sends the
base-changed basis `bK.baseChange B` to `bV.baseChange B`, index by index.

- `subspaceExtension_extensionComparison`: under this equivalence the
  embedding `subspaceExtension G V B` corresponds to
  `kernelBaseChangeLinearEquiv k K G B ∘ subspaceExtension G_K V_K B`. Both
  sides are `B`-linear, so it suffices to compare them on the basis
  `bK.baseChange B`. There it is the identity
  `schemeScalarExtension_base_naturality`, which identifies the image of
  `schemeScalarExtension G (1 ⊗ x)` in `Lie(G)(B)` with the image of `x`.
- `isAdjointStable_baseChange`: if `V` is stable for `l` (in the sense of
  `IsAdjointStable`), then `V_K` is stable for `l_K`. For a `K`-algebra `B`,
  give `B` the `k`-algebra structure through `K`. A `B`-point `m` of `M_K`
  corresponds to the `B`-point `affineBaseChangeEquiv k K M B m` of `M`. The
  comparison `kernelBaseChangeLinearEquiv` intertwines the adjoint operators
  (`kernelBaseChangeLinearEquiv_adjoint`, `affineBaseChangeEquiv_target`), so
  stability of `V` gives stability of `V_K`.
- `extensionComparison_stableOperator`: the comparison intertwines
  `stableOperator` of `V_K` at `m` with `stableOperator` of `V` at the
  corresponding point of `M`. The proof uses injectivity of
  `subspaceExtension` and the same compatibilities.
- `det_stableOperator_baseChange`: hence the two induced operators have the
  same determinant (`LinearMap.det_conj`).

## Base change of the character

`baseChange_stableDeterminantCharacter`: if `M.X.left` is affine, then

```
rationalCharacters.baseChange b (stableDeterminantCharacter hV) =
  stableDeterminantCharacter hVK
```

for any stability proofs `hV` of `V` and `hVK` of `V_K`. Characters are
compared by their values on points (`rationalCharacters.ext_characterEval`).
Since `M_K` is affine, every point factors through an affine point by
`essImage_algSpec`, so it suffices to compare values at affine points over
`K`-algebras `B`. There
`rationalCharacters.characterEval_baseChange_affine` (module
`Langlands.GroupScheme.Lie.ActionBaseChange`) reduces the left side to the
value of the original character at the corresponding `B`-point of `M`. Both
values are then determinants of the induced operators
(`stableDeterminantCharacter_eval_affine`, `stableMatrix_det`), and these are
equal by `det_stableOperator_baseChange`.

## Provenance

The module is derived. It is the subspace version of the base-change
compatibility `AutomorphicAction.determinantCharacter_baseChange` (module
`Langlands.GroupScheme.Lie.ActionBaseChange`) for determinant characters of
whole Lie algebras, and it follows the same reduction to affine points. No
finiteness, separability or normality of `K/k` is assumed.
