# Preadditive varying-group equivariant diagrams

This internal construction equips the existing category
`Langlands.EquivariantDiagram D C` with pointwise addition on morphisms.
It is a prerequisite for using additive and homological constructions on
compatible coefficient diagrams with varying groups.

The index category `I`, its morphisms, the groups in `D : I ⥤ GrpCat`,
and the objects and morphisms of the coefficient categories `C` and `E`
have seven independent universes. No finiteness, topology, or continuity
condition is imposed on the groups or the index category.

## Construction and intrinsic laws

Assume that `C` is preadditive. A morphism `f : M ⟶ N` in the existing
equivariant diagram category is a natural transformation `f.hom` satisfying
the action commutation equation at every index and every group element.
Zero, addition, negation, subtraction, natural-number multiplication and
integer multiplication are defined using the corresponding operations on
`f.hom`. Bilinearity of composition in `C` proves that each resulting
natural transformation still satisfies the action commutation equation.
The existing functor-category structure supplies naturality.

`preadditive` transfers the abelian-group laws along the injective map
`f ↦ f.hom`. Its two remaining fields are bilinearity of composition,
proved by the corresponding laws in the underlying functor category.
The lemmas `zero_hom`, `add_hom`, `neg_hom`, `sub_hom`, `nsmul_hom` and
`zsmul_hom` identify the operations with those on natural transformations.
`homAddHom` packages this inclusion as an additive group homomorphism,
and `sum_hom` identifies finite sums with their underlying finite sums.

`forget_additive` proves that the existing faithful forgetful functor
to `I ⥤ C` is additive. `evaluation_additive` proves that evaluation at
each index is additive into Mathlib's category `Action C (D.obj i)`,
using its existing preadditive structure.

If both `C` and `E` are preadditive and `F : C ⥤ E` is additive,
`mapFunctor_additive` proves that the existing postcomposition functor
on equivariant diagrams is additive: its action on each component is
`F.map`, which preserves addition.

`postcompose_additive` needs only `E` preadditive. It concerns addition
of natural transformations between arbitrary coefficient functors
`C ⥤ E`; their induced transformations between equivariant-diagram
functors preserve this addition componentwise. This assertion does not
require those coefficient functors themselves to be additive.

## Provenance and scope

This is a derived categorical construction from the published
`EquivariantDiagram` and `EquivariantDiagramFunctor` definitions.
The Hom-group transfer follows the existing Mathlib
`CategoryTheory.Action.Limits` construction for actions; natural
transformations use Mathlib's
`CategoryTheory.Preadditive.FunctorCategory` structure. All equivariance
and bilinearity obligations are proved in Lean.

The file constructs a preadditive structure, without asserting that
the category has biproducts, kernels, cokernels, or is abelian.
It does not construct coefficient complexes, prove exactness of
completion or associated sheaves, or identify any Harris cohomology.
