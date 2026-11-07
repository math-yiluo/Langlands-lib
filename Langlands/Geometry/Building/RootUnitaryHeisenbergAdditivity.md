# Additivity of the Heisenberg cocycle in field coordinates

The published structure `HeisenbergUnitaryData` (module
`Geometry/Building/RootUnitaryHeisenbergAssembly`) has a field `form_add`. It states that the
cocycle of a Heisenberg normal form, written in the field coordinates `first` and `second`, is
additive in its second argument. This module proves that this field holds automatically:
for any additive coordinates of `V(k)` and of `U_{2a}(k)`, the cocycle in these coordinates is
additive in its second argument. So a constructor of `HeisenbergUnitaryData` need not prove
`form_add` separately.

Provenance: the module is internal. It uses the published bilinearity of the cocycle in
weight coordinates (`HeisenbergNormalForm.isBilinearVectorPairing_cocycle`, module
`RootHeisenbergNormalForm`).

All declarations live in namespace `Langlands.Geometry.Building`.

## Setting

`k` is a field, `S` a commutative group scheme over `Spec k`, and `G` a smooth affine group
over `Spec k` with `i : S.toGrp ⟶ G`. For a character `a`, `j : U ⟶ G` and
`j₂ : U₂ ⟶ G` represent the root functors of `a` and `2 • a`, and
`C : DoubleRootCommutatorPairing i a hj hj₂` is the quotient datum, with quotient `C.V`.
`M : HeisenbergNormalForm C` is a Heisenberg normal form with cocycle
`M.cocycle : C.V × C.V ⟶ U₂`. The hypotheses `hS : IsSplitTorus S`, `ha : a ≠ 0` and
`hhigh : ∀ n ≥ 3, n • a ∉ relativeRoots i` are as in the published modules.

## Results

- `HeisenbergNormalForm.cocycle_lift_mul_right M hS ha hhigh`: for every test scheme `T` and
  points `x, y, y'` of `C.V` over `T`,
  `M.cocycle (x, y y') = M.cocycle (x, y) · M.cocycle (x, y')`. Proof: choose weight
  coordinates `e` of weight `a` on `C.V` (field `C.weightVectorStructure`) and weight
  coordinates `e'` of weight `2 • a` on `U₂` (published
  `weightVectorCoordinatesOfNoHigherRoots`). In these coordinates the cocycle is bilinear,
  and in particular additive in its second argument. Since `e'` is injective, this gives
  the identity.
- `HeisenbergNormalForm.form_add_of_cocycle_eq M hS ha hhigh first second form cocycle_eq`.
  Here `E` is an additive group, `H` an additive subgroup of `E`,
  `first : Multiplicative E ≃* V(k)` and `second : Multiplicative H ≃* U₂(k)` are group
  isomorphisms, and `form : E → E → E` satisfies `cocycle_eq`: `form x y` is the image under
  `second⁻¹` of the cocycle at `(first x, first y)`, read in `E`. Then
  `form x (y + y') = form x y + form x y'`. Proof: `first` and `second` are multiplicative,
  so this is `cocycle_lift_mul_right` on rational points.

The hypotheses on `first`, `second`, `form` and `cocycle_eq` are exactly the corresponding
fields of `HeisenbergUnitaryData`.

## Scope

The module proves only the additivity field. The fields `form_trace` and `form_nonsymm`, the
field coordinates and the character data of `HeisenbergUnitaryData` are not treated.
