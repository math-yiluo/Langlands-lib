# Contravariant nondegenerate dual functors

Worker 1156 constructed this functor pair using Worker 1149's actual dual and
pullback constructions. Import `Langlands.Algebra.NonUnitalModuleDualFunctor`.
All declarations below are in `Langlands.Algebra.NonUnitalModuleDual`.

The governing source is Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, I.4.1 opening, printed page 22 /
PDF page 28: registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original-action conventions are printed pages 5–7 / PDF pages 11–13.
The canonical scalar construction is I.2.1, printed page 14 / PDF page 20.
The opening and adjacent duality assertions on PDF pages 28–29 were read,
together with the conventions and canonical scalar passage. The supplementary
registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, contains nearby duality/admissibility corrections and does not
change these opening constructions in the governing 2026 edition.
The source introduces both contravariant functors. The explicit bundled
interfaces, double-op transport and their named formulas are derived internal
construction details implementing those functors.

The functors have independent algebra and carrier universes `uA` and `uM`.
Their algebra data are `[NonUnitalRing A] [Module ℂ A]`,
`[IsScalarTower ℂ A A] [SMulCommClass ℂ A A]` and
`hA : IsIdempotented A`. Objects retain their specified additive group and
original nonunital action. Each full dual uses precisely the canonical
`NondegenerateScalars.complexModule` recovered from that action and
nondegeneracy, without supplying a pre-existing complex module on the object.
There is no unit-action, dimension, admissibility, nontriviality, faithfulness
or anti-involution hypothesis. Both functors use the existing
`NondegenerateModuleCat` and `RightNondegenerateModuleCat`; no parallel
categories are introduced.

For a left object `M`, `dualObject hA M` bundles exactly
`Dual hA M.property` as an object of `RightNondegenerateModuleCat A`.
Its action is the inherited action from the actual full dual, and its
nondegeneracy is `isNondegenerate hA M.property`.
`dualObject_carrier` gives equality of the carrier with that actual subtype.
`dualObject_smul_val` identifies the entire included functional after acting
by `op a` with composition by
`NondegenerateScalars.toLinearEndHom ℂ hA M.property a`.
`dualObject_smul_apply` evaluates this as `φ.val (a • m)`.
The scalar structures and their comparison are supplied by the imported
`NonUnitalModuleDual` pair.

`leftToRightFunctor hA` has type

```lean
(NondegenerateModuleCat A)ᵒᵖ ⥤ RightNondegenerateModuleCat A
```

It sends the categorical opposite of `M` to `dualObject hA M`. For an
original intertwiner `f : M ⟶ N`, it sends `f.op` to the original right
intertwiner `pullback hA M.property N.property f.hom`. Its identity and
composition fields use `pullback_id` and `pullback_comp`, respectively,
after extensionality in the existing full subcategory. Thus composition
reversal is inherited from the actual bundled pullbacks.
`leftToRightFunctor_obj` and `leftToRightFunctor_obj_carrier` state the exact
object and carrier formulas; `leftToRightFunctor_obj_smul_apply` states the
action formula on its elements.
`leftToRightFunctor_map_hom` is equality of the entire underlying bundled
intertwiner with `pullback`. `leftToRightFunctor_map_val` identifies its
entire included functional with composition by
`NondegenerateScalars.complexToLinearMap hA M.property N.property f.hom`.
`leftToRightFunctor_map_apply` evaluates this as `φ.val (f.hom m)`.
The formal formulas project `NonUnitalModuleHom.toAddMonoidHom` explicitly
to expose the function of a morphism of the original category.

Two different opposite constructions occur here. The multiplicative
opposite ring `Aᵐᵒᵖ` reverses multiplication and encodes a right algebra
action. The categorical opposite `(NondegenerateModuleCat A)ᵒᵖ` reverses
morphisms. Dualizing a right object first yields a module over the
multiplicative double opposite; returning it to `A` requires an actual
transport of the action.

`fromDoubleOppositeAction` performs this transport on the same additive
carrier by

```text
a • m = MulOpposite.op (MulOpposite.op a) • m.
```

`fromDoubleOppositeAction_smul` states this formula. The action laws follow
from the given double-op laws by applying the opposite identities twice.
`fromDoubleOpposite_isNondegenerate` transports a fixing idempotent by
`e ↦ e.unop.unop`; its proof transports the idempotence equation and retains
the fixing equation. `fromDoubleOpposite_isScalarTower` and
`fromDoubleOpposite_smulCommClass` retain any given compatible complex
scalars on this same carrier.

`fromDoubleOppositeMap` keeps the whole additive map of a double-op
intertwiner, and its new intertwining field specializes the old one to
`op (op a)`. `fromDoubleOppositeMap_toAddMonoidHom` and
`fromDoubleOppositeMap_apply` state those exact additive-map and evaluation
identities. `fromDoubleOppositeMap_zero` and `fromDoubleOppositeMap_add`
follow by original-Hom extensionality and pointwise evaluation.
`fromDoubleOppositeFunctor` bundles this transport between the existing
nondegenerate module categories over `Aᵐᵒᵖᵐᵒᵖ` and `A`.
Its identity and composition laws reduce to the unchanged functions.
`fromDoubleOppositeFunctor_obj_carrier`,
`fromDoubleOppositeFunctor_obj_smul` and
`fromDoubleOppositeFunctor_map_hom` expose the unchanged carrier, explicitly
transported action and complete transported map. The action formula names
the target's action structure explicitly, so a competing source action
on the same carrier cannot change its meaning.

For a right object `M`, `rightDualObject hA M` is this transport applied to
`dualObject hA.op M`. Its carrier is exactly `Dual hA.op M.property`,
the actual nondegenerate part of the full canonical-complex dual of `M`,
as stated in `rightDualObject_carrier`.
`rightDualObject_smul_val` identifies its entire included functional after
acting by `a : A` with composition by the original right action of `op a`.
`rightDualObject_smul_apply` states `(a • φ).val m = φ.val (op a • m)`.
The output is an actual left `A`-module with this transported action.

`rightToLeftFunctor hA` has type

```lean
(RightNondegenerateModuleCat A)ᵒᵖ ⥤ NondegenerateModuleCat A
```

It is `leftToRightFunctor hA.op ⋙ fromDoubleOppositeFunctor`, where the
latter is the explicit transport just described.
`rightToLeftFunctor_obj`, `rightToLeftFunctor_obj_carrier` and
`rightToLeftFunctor_obj_smul_apply` state its exact object, actual subtype
carrier and left action formulas.
`rightToLeftFunctor_map_hom` identifies its whole original left
intertwiner with `fromDoubleOppositeMap` of the actual right-object
pullback. `rightToLeftFunctor_map_val` gives the entire included functional
as composition with the automatically complex-linear original right
intertwiner, and `rightToLeftFunctor_map_apply` gives
`φ.val (f.hom m)`. Composition of the two implemented functors supplies
its identity and composition laws.

These are constructions and intrinsic laws. Fixed-part dual isomorphisms,
exactness, bidual evaluation or injectivity, anti-involution transport,
forgetful/adjoint/completion comparisons and admissible reflexivity remain
separate successor work.
