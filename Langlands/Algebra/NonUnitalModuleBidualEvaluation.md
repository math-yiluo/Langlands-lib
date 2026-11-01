# Canonical evaluation into the actual nondegenerate bidual

Worker 490 constructed this pair; Worker 691 contributed the companion
complete-declaration, universe and explicit-structure checks. Import
`Langlands.Algebra.NonUnitalModuleBidualEvaluation`. All construction names
below belong to `Langlands.Algebra.NonUnitalModuleDual`.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, I.4.1, printed pages 22–23 /
PDF pages 28–29, especially the construction in the proof of the unnumbered
corollary on printed page 23. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital conventions, printed pages 5–7 / PDF pages 11–13,
and canonical complex scalars in I.2.1, printed page 14 / PDF page 20,
were also read. The registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was checked for nearby duality corrections. Its nonzero-vector
correction concerns separation, not the evaluation construction. The
2026 edition governs; no source-specific project errata file was found
at the source-audit date, 1 November 2026.

The inputs are the specified `[NonUnitalRing A] [Module ℂ A]`,
`[IsScalarTower ℂ A A] [SMulCommClass ℂ A A]`,
`hA : IsIdempotented A`, and a specified additive
`[AddCommGroup M] [NonUnitalModule A M]` with
`hM : IsNondegenerate A M`. There is no supplied complex module on `M`.
Every required scalar structure is precisely the published
`NondegenerateScalars.complexModule` recovered from the relevant original
action and nondegeneracy proof. The algebra, source and target universes
`uA`, `uM` and `uN` are independent. There is no dimension, nontriviality,
unit-action, admissibility, faithfulness or anti-involution hypothesis;
zero algebra and module carriers are allowed.

`Bidual hA hM` is exactly `Dual hA.op (isNondegenerate hA hM)`,
the actual nondegenerate second-dual subtype of the published
`Dual hA hM`. `bidual_carrier` records this equality. Its original
`A` action, `bidualAction`, is precisely `fromDoubleOppositeAction`
applied to the inherited double-opposite action.
`bidualAction_eq` states equality of the complete action structures.
`bidualAction_smul_val` identifies the entire resulting functional as
composition with
`NondegenerateScalars.toLinearEndHom ℂ hA.op
  (isNondegenerate hA hM) (op a)`;
`bidualAction_smul_apply` gives
`(a • Φ).val φ = Φ.val (op a • φ)`.
The named actions are installed locally. The pair adds no global action
or complex scalar instance.

`fullEvaluation hA hM m` is the actual complex-linear functional on
the actual first dual sending `φ` to `φ.val m`. Its definition explicitly
installs the recovered scalars on `M` and on `Dual hA hM`.
Additivity in `φ` is pointwise. Scalar linearity is exactly the published
`canonical_smul_apply`, which identifies the recovered scalars of the
first dual with its inherited pointwise scalars.
`fullEvaluation_coe` is equality of its entire underlying function with
`fun φ => φ.val m`; `fullEvaluation_apply` is the pointwise formula.
`fullEvaluationLinear` makes the assignment complex linear in the
original vector `m`, for the recovered scalar module on `M`.
Its additive and scalar laws use full-dual extensionality followed by
the corresponding laws of `φ.val`. `fullEvaluationLinear_coe` identifies
the complete underlying function with `fullEvaluation`.

`fullEvaluation_fixed` starts with an original
`e : Idempotent A` and `(e : A) • m = m`. After full-dual extensionality,
its double-opposite fixing equation reduces to

```text
φ.val ((e : A) • m) = φ.val m.
```

The supplied original fixing equation proves this identity.
`fullEvaluation_mem` obtains such an `e` from `hM m`, forms the actual
idempotent `op (op (e : A))`, transports its idempotence equation by
congruence, and uses `fullEvaluation_fixed`. This proves membership in
`nondegeneratePart hA.op.op
  (FullDual hA.op (isNondegenerate hA hM))`.
Thus membership is constructed using an original local fixer of `m`;
it does not use fixed-part duality or separation.

`bidual_isNondegenerate` is the intrinsic nondegeneracy law for the
transported target. It applies the published
`fromDoubleOpposite_isNondegenerate` to the actual second dual.
`evaluation hA hM` is the original
`NonUnitalModuleHom A M (Bidual hA hM)` with
`m ↦ ⟨fullEvaluation hA hM m, fullEvaluation_mem hA hM m⟩`.
Its zero and additive laws follow by subtype/functional extensionality
and the linear-map laws of `φ.val`. For original-action intertwining,
both sides evaluated at `φ` reduce definitionally to `φ.val (a • m)`.
`evaluation_val` identifies the entire included functional;
`evaluation_apply` gives `(evaluation hA hM m).val φ = φ.val m`.
`evaluation_coe` states equality of the entire subtype function, and
`evaluation_map_smul` exposes the original-action intertwining law.

`evaluationLinear` packages the same additive map for exactly the
recovered source scalars and the recovered target scalars coming from
`hA` and `bidual_isNondegenerate hA hM`. It uses the published automatic
linearity conversion `NondegenerateScalars.complexToLinearMap` on
`evaluation`. `evaluationLinear_toAddMonoidHom` is equality of the whole
additive maps, and `evaluationLinear_apply` retains the exact evaluation
formula.

For an original `f : NonUnitalModuleHom A M N`,
`doublePullback hA hM hN f` first forms the actual
`pullback hA hM hN f`, then pulls back along that map over `Aᵐᵒᵖ`,
then applies `fromDoubleOppositeMap`.
`doublePullback_eq` states the equality of these complete original
bundled maps. `doublePullback_val` identifies the entire included
functional with the actual full second pullback;
`doublePullback_apply` gives

```text
(doublePullback hA hM hN f Φ).val φ =
  Φ.val (pullback hA hM hN f φ).
```

`evaluation_naturality` is equality of whole original intertwiners:

```text
(doublePullback hA hM hN f).comp (evaluation hA hM) =
  (evaluation hA hN).comp f.
```

Original-Hom extensionality, then second-dual extensionality, reduces
the two composites to the same value `φ.val (f m)`. This law retains
independent source and target universes.

`bidualFunctor hA` is definitionally the existing composite
`(leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA` on the existing
`NondegenerateModuleCat.{uA,uM} A`; `bidualFunctor_eq` states the exact
functor equality. Here `rightOp` reverses categorical variance, whereas
`fromDoubleOppositeAction` transports the multiplicative double-opposite
ring action. These are distinct operations.
`bidualFunctor_obj`, `bidualFunctor_obj_carrier` and
`bidualFunctor_obj_action` identify the actual object, carrier and
complete original action with `rightDualObject hA (dualObject hA M)`,
`Bidual hA M.property` and `bidualAction hA M.property`, respectively.
`bidualFunctor_obj_smul_val` and `bidualFunctor_obj_smul_apply` expose
the whole functional and its value under that explicitly projected
bundled action. `bidualFunctor_map_hom` identifies the whole map with
`doublePullback`; `bidualFunctor_map_val` and
`bidualFunctor_map_apply` expose its whole included functional and its
value.

`evaluationNatTrans hA` has type
`𝟭 (NondegenerateModuleCat.{uA,uM} A) ⟶ bidualFunctor hA`.
Its component is exactly `ObjectProperty.homMk
  (evaluation hA M.property)`.
Naturality is the original whole-map equality
`evaluation_naturality`, with the orientation required by Mathlib's
natural-transformation field. `evaluationNatTrans_app_hom` and
`evaluationNatTrans_app_toAddMonoidHom` identify the complete original
intertwiner and additive map with `evaluation`.
`evaluationNatTrans_app_val` identifies its entire included functional,
and `evaluationNatTrans_app_apply` evaluates it at each actual first-dual
element. These component formulas explicitly project
`NonUnitalModuleHom.toAddMonoidHom` from the published category.
Where original and transported structures share a carrier, the
map equalities install `bidualAction` explicitly.

The companion `NonUnitalModuleBidualEvaluationChecks` checks complete
unapplied declaration types, the unequal algebra/carrier universe
directions, unequal source and target universes for original naturality,
explicit structure choices, opposite-ring specialization and zero
carriers. These are elaboration and interface checks of the implemented
construction, not additional assumptions.

The canonical evaluation map and original local-fixer argument come
from the source. The named carrier/action/map interfaces, recovered
linear packaging, whole-map identities and natural-transformation
packaging are derived internal details implementing that construction.
Applying the generic construction to `Aᵐᵒᵖ` gives evaluation for original
right modules. This pair does not identify that specialization with the
differently transported actual right categorical composite.
Injectivity, separation, monomorphism, surjectivity, reflexivity,
fixed-part isomorphisms and duality exactness remain separate
statements and proofs.
