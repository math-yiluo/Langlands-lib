# Finite connected families from supplied torus and root models

This is an internal construction for the neutral-model argument. It packages
supplied geometric models and proves an exact generated-point identity. It
does not assert existence of the supplied models or maps, identify the
generated subgroup with the zero-point fixer, or prove the parahoric-model
statement.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`, and
`O = fixedFieldIntegers F`, all in the arbitrary universe `u`. Let `G` be an
affine `K`-group, `C` supplied maximal-unramified building data for `G`, and `E`
supplied unramified zero-subgroup data. Fix an apartment point `x`, an apartment
subset `Ω`, and an actual ambient integral model `N` of `G` over `O`.

`TorusRootModelFamilyData C E x Ω N` consists of:

- An actual smooth affine model of `E.T` over `O` with geometrically connected
  fibres, integral points exactly `E.torusIwahori`, and a compatible actual
  integral-model map into `N` extending `E.i`.
- For every actual relative root `a` of `C.S`, a `RootFiltrationModelData` at
  `x` and depth `C.apartment.rootFixerDepth a x Ω`, and an actual compatible
  map of this model into `N` extending its specified generic inclusion.

The root-model fields retain their all-test generic root-representation
condition, actual smooth affine integral models, geometric connectedness,
and exact filtration-image equality. Integral-model maps retain compatibility
with the specified generic-fibre identifications. None of these fields is
inferred from an equality of abstract subgroups.

The option type on the actual relative roots indexes the torus by `none` and
the root model at `a` by `some a`. The definitions `genericGroup`, `model`,
`genericMap`, and `modelMap` select these actual objects. The corresponding
smoothness and geometric connectedness lemmas inspect the same two cases.

`connectedFamily` enumerates this index type by `Fin n` and yields an actual
`FiniteConnectedModelFamily N`. The root set is finite because `C` supplies a
connected reductive group, hence smoothness and local finite type, and a maximal
split torus; `relativeRootFintypeOfIsSplitTorus` applies to these data.
This constructs the finite enumeration rather than requiring a separate
finiteness premise. The torus remains present even if the root set is empty.

`integralImages_connectedFamily` proves that this enumeration preserves the
subgroup supremum defining the generated generic images, by the supremum
identity for an equivalence of index types.

For nonempty `Ω` bounded above under every real affine function,
`integralImages_eq_torus_sup_sharpFixer` proves

```text
A.connectedFamily.integralImages =
  E.torusIwahori.map (rationalPoints.map E.i) ⊔ C.sharpFixer Ω.
```

The proof splits the supremum over the option type into its torus and root
parts. It uses the supplied torus-point equality and each supplied
root-filtration point equality. The previously proved bounded-root-fixer
identity identifies each of these filtration levels with the corresponding
actual root fixer. Their supremum is the existing definition of the sharp
fixer. `torus_sup_sharpFixer_le_integralPoints` then applies the finite family's
compatible maps to put this subgroup inside `N.integralPoints`.

These results are derived from the named Library interfaces and the supplied
model data. They make no new assertion from the literature. The constructions
of the connected torus and root models, their ambient maps, finite relative
index and congruence containment remain separate obligations. Applying
`FiniteConnectedModelFamily.integralImages_eq_neutral` also requires a proof
of `ConnectedGenerationStatement`.

The maximal torus in an arbitrary `E` need not be adapted to the chosen
apartment. In particular, this file does not assert that its torus Iwahori
image fixes `Ω`, or that this image joined with the sharp fixer equals
`E.zeroPoints` intersected with the pointwise fixer. Supplying the maps above,
choosing adapted torus data, and comparing zero subgroups for different
torus data require their own arguments.
