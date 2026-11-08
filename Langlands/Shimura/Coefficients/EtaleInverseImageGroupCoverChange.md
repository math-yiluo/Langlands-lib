# Inverse image and varying-group cover comparison

This internal unit identifies genuine small-etale inverse image of a whole
varying-group cover-comparison arrow with the comparison for the actual
base-changed covers. Its proof is derived from the published
`inverseImageConstantAssociatedMap_crossCover`,
`etaleAssociatedVaryingSystemInverseImage` and
`etaleAssociatedVaryingGroupCoverIso`. It introduces no new literature assertion.

The parameters are schemes `X` and `Z` in universe `u`, an arbitrary scheme
morphism `f : Z ⟶ X`, a commutative ring `R : Type u`, an arbitrary category `I`
with independent object and morphism universes, group diagrams
`D E : I ⥤ GrpCat.{u}`, and a natural group map `φ : D ⟶ E`.
The cover diagrams are `Y : EquivariantDiagram D X.Etale` and
`V : EquivariantDiagram E X.Etale`. The given morphism
`a : Y ⟶ (groupRestriction X.Etale φ).obj V` is an actual compatible family
of equivariant morphisms of covers. Each action in both diagrams is assumed to
be a finite geometric torsor. No condition is imposed on `f`, and no comparison
isomorphism is supplied as a premise.

Write `Y'` and `V'` for their actual scheme fiber-product pullbacks along `f`.
The definition `etaleGroupCoverMapPullback` pulls back `a` using
`etaleTorsorDiagramPullback f D`. Its target is definitionally the restriction
along `φ` of `V'`. The evaluation theorem identifies each action-level component
with the actual pullback of the corresponding component of `a`. This construction
retains every deck-group map and every cover transition.

For a full coefficient diagram `M : EquivariantDiagram E (ModuleCat R)`,
write `res M` for restriction of its actions along `φ`. This keeps the original
underlying modules and all their transition maps. Write:

- `c_X(M)` for the published whole-system cover isomorphism from association
  on `V` with `M` to association on `Y` with `res M`;
- `c_Z(M)` for the corresponding isomorphism for `a' : Y' ⟶ res V'`;
- `s_V(M)` and `s_Y(res M)` for the published genuine inverse-image
  isomorphisms to association on the pulled-back covers;
- `P` for right whiskering of `I`-indexed sheaf systems by `inverseImage f R`.

The theorem `etaleAssociatedVaryingGroupCoverIso_inverseImage_hom` proves
the equality of complete system morphisms

```text
P.map(c_X(M).hom) ≫ s_Y(res M).hom
  = s_V(M).hom ≫ c_Z(M).hom.
```

Natural-transformation extensionality reduces this equality to each index.
There it is exactly `inverseImageConstantAssociatedMap_crossCover` with the
original component of `a`, group map `φ.app i`, and identity coefficient map.
Thus the square uses the original cover map and inverse-image comparisons,
without choosing new section maps.

The theorem `etaleAssociatedVaryingGroupCoverIso_inverseImage_inv` proves

```text
P.map(c_X(M).inv) ≫ s_V(M).hom
  = s_Y(res M).hom ≫ c_Z(M).inv.
```

It postcomposes with `c_Z(M).hom`, uses the first square, and cancels the
original inverse/hom isomorphism pairs and their functor images.

The selected definition
`etaleAssociatedVaryingGroupCoverInverseImageArrowIso` constructs an
isomorphism in the arrow category of complete `I`-indexed module-sheaf systems:

```text
Arrow.mk(P.map(c_X(M).hom)) ≅ Arrow.mk(c_Z(M).hom).
```

Its source endpoint is `s_V(M)` and its target endpoint is `s_Y(res M)`;
the commuting square is the forward theorem above. These endpoints are
independently constructed genuine inverse-image isomorphisms. Since all arrows
are morphisms of complete systems, they retain every index transition.
The constructions use the existing natural isomorphisms in the full coefficient
diagram, so the given coefficient maps and reductions remain unchanged.

This is a generic compatibility prerequisite for normalizing CM
coefficient-system inverse-image comparisons. It does not itself prove the
CM specialization, inverse-image composition normalization, lattice independence,
Hecke compatibility, representability, or the Harris canonical-model and
existence obligations.
