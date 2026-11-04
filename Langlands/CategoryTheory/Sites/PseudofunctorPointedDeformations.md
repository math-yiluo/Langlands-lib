# Pointed deformations over general test objects

This is an internal categorical construction from Mathlib's structured-arrow
categories and the identity and composition comparisons of an ordinary
category-valued pseudofunctor. It introduces no external mathematical premise.
The construction will be used with the actual relative Picard pseudofunctor;
no deformation hull or algebraicity theorem is asserted here.

## Objects and morphisms

Fix a category `C : Type u` with morphisms in `Type v`, a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}`, an object `T₀` of `C`, and an
actual object `M` of `F(T₀)`. A test `T : Under T₀` is an object `T.right`
with a specified arrow `i_T : T₀ ⟶ T.right`.

`Deformations F M T` is the actual category
`StructuredArrow M (F.map i_T.op.toLoc).toFunctor`. Its objects are objects
`A.right` of `F(T.right)` together with a specified arrow
`A.hom : M ⟶ F(i_T)(A.right)`. Its morphisms are arrows between the underlying
objects whose pullbacks commute with those specified arrows. The general
construction does not assume that the fibre categories are groupoids, so the
specified arrows need not be isomorphisms in this module.

## Restriction with the specified arrow

A map of tests `q : T ⟶ U` has an underlying arrow `q.right` with
`i_T ≫ q.right = i_U`. `restrictionComparison F q` is the original flexible
composition comparison `F.mapComp'`, with precisely this equality supplied:

```text
F(i_U) ≅ F(q.right) ⋙ F(i_T).
```

`restrict F M q` is `StructuredArrow.map₂` with underlying functor
`F(q.right)`, the identity functor on `F(T₀)`, identity on `M`, and the hom
of that comparison. Thus its underlying object and morphism are ordinary
restriction, as recorded by `restrict_obj_right` and `restrict_map_right`.
`restrict_obj_hom` proves the exact formula

```text
(restrict q A).hom = A.hom ≫ (restrictionComparison q).hom.app A.right.
```

In particular, a chosen reduction arrow is part of the construction and of its
compatibility laws throughout.

## Identity, composition and coherence

`restrictIdIso` compares restriction by an identity to the identity functor.
Its underlying component is `F.mapId`. `restrictCompIso q r` compares
restriction along `q ≫ r` with restriction first along `r`, then along `q`.
Its underlying component is the original `F.mapComp'`. Their structured-arrow
compatibility follows from the original pseudofunctor's unit and associativity
laws. The component equations `restrictIdIso_hom_app_right`,
`restrictCompIso_hom_app_right` and `restrictCompIso_inv_app_right` identify
the underlying homs and inverses with those original comparisons.

`restrict_associativity`, `restrict_left_unitality` and
`restrict_right_unitality` prove all three coherence equations. The implemented
proofs use extensionality of natural transformations and structured-arrow
morphisms to reduce them to the coherence equations of `F`. Equalities of
composite or identity base arrows contribute their required `eqToHom`
transports. These are retained in the equations.

`pseudofunctor` packages these data using `LocallyDiscrete.mkPseudofunctor`:
its source is `LocallyDiscrete (Under T₀)ᵒᵖ`. Its values are exactly the
structured-arrow categories above, its arrows are the stated restriction
functors, and its comparison isomorphisms are the stated ones. The proof of
its laws only converts between Cat's two-morphism wrappers and the proved
natural-transformation equations. The four universes are unrestricted.

## Scope

The module constructs categories and coherent restriction on all pointed tests.
It contains no Artinian, smoothness, representability, effectivity, versality,
algebraization or atlas-existence assertion. Groupoid structure in the Picard
specialization is supplied separately by the invertibility of actual bundle
arrows.
