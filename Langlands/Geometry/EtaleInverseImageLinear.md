# Linear structure of the constructed etale inverse-image adjunction

This module equips the constructed arbitrary-morphism inverse image
with its additive and `R`-linear structure and packages its actual
adjunction Hom correspondence as an `R`-linear equivalence.

The base map is any `f : Z ⟶ X`. Both schemes, the commutative
ring `R`, and the module carriers have universe `u`. There are
no etaleness, field, finite-type, Noetherian, finiteness, coefficient
freeness or local-constancy hypotheses.

This is internal categorical infrastructure derived from the actual
adjunction in `EtaleInverseImage`, the pointwise linearity of
geometric direct image, Mathlib's additive-adjunction results,
and the unit and counit formulas for the Hom correspondence.
It makes no new external-literature claim.

## Additivity and linearity

Write `L_f := inverseImage f R` and
`D_f := EtaleDirectImage.directImage f (ModuleCat.{u} R)`.
The actual geometric direct-image functor already preserves
addition and `R`-scalar multiplication on sheaf morphisms.

`inverseImage_additive` applies
`Adjunction.left_adjoint_additive` to the constructed adjunction
`L_f ⊣ D_f`. It therefore proves additivity of this particular
constructed left adjoint.

`inverseImage_linear` proves
`L_f.map (r • a) = r • L_f.map a` for every coefficient scalar
and every sheaf morphism. Injectivity of the actual adjunction
Hom equivalence reduces the equation to the right-hand Hom
module. The unit formula, unit naturality, linearity of `D_f`,
and linearity of composition prove that equation. No scalar
compatibility of `L_f` is assumed.

## The linear Hom correspondence

For source and target module sheaves `F` and `G`,
`homLinearEquiv f R F G` is

```text
(L_f.obj F ⟶ G) ≃ₗ[R] (F ⟶ D_f.obj G).
```

Its underlying equivalence is the existing constructed adjunction
Hom equivalence. Mathlib's `Adjunction.homAddEquiv` supplies the
additive structure; the unit formula and linearity of direct
image prove scalar compatibility.

`homLinearEquiv_apply` identifies its forward map as

```text
a ↦ η_F ≫ D_f.map a,
```

where `η` is the actual constructed adjunction unit.
`homLinearEquiv_symm_apply` identifies the inverse as

```text
b ↦ L_f.map b ≫ ε_G,
```

where `ε` is the actual counit. The inverse laws and naturality
come from the same underlying adjunction, rather than an
independently supplied bijection.

This construction concerns ordinary module sheaves. Arbitrary-map
finite-limit preservation of inverse image, equivariant and smooth
sheaf adapters, Ext or derived adjunctions, support comparisons,
algebraic-closure base change, torsor coefficient comparisons and
Harris specialization remain separate.
