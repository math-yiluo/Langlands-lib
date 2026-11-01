# Renard's right-module pseudo-forgetful and induction functors

This internal additive construction specializes `Langlands.Algebra.NondegenerateRightHomFunctor` on the original carrier `B`. It uses the specified original actions and explicitly selects the published regular action needed by each specialization. The construction is valid for arbitrary associative nonunital rings under the stated hypotheses.

## Sources and provenance

The governing source is Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The consulted passages are:

- Conventions, printed pp.5–7 / PDF11–13: nonunital modules, commuting bimodule actions, idempotented rings, idempotent fixation and nondegenerate right modules.
- I.2.3, printed pp.16–18 / PDF22–24: Hom functors, their nondegenerate parts, and the pseudo-forgetful and induction specializations for complex algebras.
- I.4.2, printed pp.23–24 / PDF29–30: the right-module versions of these functors in the tensor-duality comparisons.

The supplementary registered errata `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF1–2 and PDF18–19, were also read. Their corrections to adjunction orientation, the object in the I.4.2 statement, and the order of Hom-map composition do not provide a coefficient-compatibility hypothesis for the tensor-dual comparisons.

The explicit original-action interfaces and arbitrary-ring additive generality are internal derived infrastructure. The implementation reuses `NonUnitalBimoduleHomActions.rightSourceAction`, the original `rightSourceHom` and `rightSourceMap` from `NonUnitalBimoduleHomNaturality`, and the actual part, restriction and inclusion construction packaged by `NondegenerateRightHomFunctor`. It also follows the published left-module `RenardHomFunctors` specialization pattern. Worker 633 wrote this specialization unit using Worker 1151's general right-Hom construction.

## Right-module pseudo-forgetful functor

Let `A` and `B` be nonunital rings. Supply a left `A`-action on the original additive group of `B`. The local instance `pseudoSourceRight` selects exactly `NonUnitalModule.rightRegular B`, so the right `B`-action on this fixed source is multiplication `b · c = b * c`. The witness `hAB : ActionsCommute A B B` refers to precisely these two actions.

For a right `B`-module `M`, the ambient Hom is exactly `NonUnitalModuleHom B.op B M`, with its published pointwise additive group. `rightPseudoAction hAB` is exactly the named `rightSourceAction hAB`. Its whole endomorphism at `op a` is `precomposeAddHom (hAB.leftActionHom a)`, and evaluation is

```text
(op a • φ)(b) = φ(a • b).
```

With `hA : IsIdempotented A`, `rightPseudoPart hAB hA M` is the actual `homPart hAB hA M`, hence `nondegeneratePart hA.op (rightSourceHom hAB M)`. Membership is equivalent to

```text
there exists e : Idempotent A such that
  for every b : B, φ((e : A) • b) = φ(b).
```

This equivalence specializes the general original-ring idempotent correspondence. It requires one idempotent fixing the entire Hom value.

`rightPseudoF hAB hA` is definitionally `restrictedFunctor hAB hA`, with the whole-functor equality

```text
nondegenerateInclusion B.op ⋙
  (ambientFunctor hAB ⋙ nondegeneratePartFunctor hA.op).
```

Its type is `NondegenerateModuleCat B.op ⥤ NondegenerateModuleCat A.op`. Its bundled object uses `nondegeneratePart_isNondegenerate hA.op`. The object and carrier interfaces expose the actual part subtype. The group equality names the inherited additive subgroup group; the action equality names the inherited subtype module. Subtype scalar values and their evaluations retain the specified residual action above.

For an original right-`B`-linear map `f : M → N`, `rightPseudoMap` is exactly `partMap hAB hA f`, namely `(ambientMap hAB f).restrictNondegeneratePart hA.op`. Here the ambient map is the published `rightSourceMap hAB hAB (NonUnitalBimoduleHom.id A B B) f`, with entire additive map `postcomposeAddHom f`. The specialization exposes the complete restriction and its underlying additive map. Its subtype value is `f.comp φ.val`, and its evaluation at `b` is `f(φ.val(b))`. The bundled functor maps expose the same whole restriction, subtype value and evaluation. Additivity is inherited from the actual restricted general functor.

`rightPseudoInclusion` is exactly the general `restrictedInclusion hAB hA`, obtained by whiskering the published part inclusion first by the ambient functor and then by the input inclusion. It has target `nondegenerateInclusion B.op ⋙ ambientFunctor hAB`. Its entire component is the actual submodule inclusion, its additive map is the subgroup inclusion, and its value is `φ.val`. Naturality is the equality of whole original right-`A`-linear maps

```text
ambientMap(f) ∘ subtype_M = subtype_N ∘ rightPseudoMap(f).
```

The direct construction requires only the supplied left action, its commutation with the selected right regular action, and idempotentedness of `A`. In particular it uses no supplied right `A`-action and no idempotentedness of `B`. `rightPseudoFOfNondegenerate` additionally accepts `IsNondegenerateBimodule A B B` for exactly the selected actions and returns the same direct functor by definition. That adapter does not derive bimodule nondegeneracy from any ring homomorphism.

## Right-module induction

Supply a right `A`-action on the original additive group of `B`. The local instance `inductionSourceLeft` selects exactly `NonUnitalModule.regular B` on the left, so `b • b' = b * b'`. The witness `hBA : ActionsCommute B A B` refers to this selected left regular action and the supplied right `A`-action.

For a right `A`-module `M`, the ambient carrier is exactly `NonUnitalModuleHom A.op B M`, with the published pointwise group. `rightInductionAction hBA` is exactly `rightSourceAction hBA`. The entire endomorphism at `op b` is `precomposeAddHom (hBA.leftActionHom b)`, and

```text
(op b • φ)(b') = φ(b * b').
```

With `hB : IsIdempotented B`, `rightInductionPart hBA hB M` is exactly `homPart hBA hB M`. Its original-ring membership criterion is

```text
there exists e : Idempotent B such that
  for every b' : B, φ((e : B) * b') = φ(b').
```

`rightI hBA hB` is definitionally `restrictedFunctor hBA hB`, with whole-functor equality

```text
nondegenerateInclusion A.op ⋙
  (ambientFunctor hBA ⋙ nondegeneratePartFunctor hB.op).
```

Its type is `NondegenerateModuleCat A.op ⥤ NondegenerateModuleCat B.op`. Its object is bundled using the actual part and `nondegeneratePart_isNondegenerate hB.op`. The carrier, subgroup group, inherited subtype module, subtype scalar value and evaluation interfaces expose exactly these structures.

`rightInductionMap` is exactly the restriction of the original ambient postcomposition map by `restrictNondegeneratePart hB.op`. Its underlying additive-map equality, subtype value `f.comp φ.val`, and evaluation formula are explicit; the bundled functor map has the same interfaces. Additivity comes from the restricted general functor. `rightInductionInclusion` is exactly `restrictedInclusion hBA hB`, with the actual submodule inclusion as its whole component, subgroup inclusion as its additive map, value `φ.val`, and whole-map naturality with respect to the original right-`B` action.

The direct induction construction uses only the supplied right `A`-action, its commutation with the selected left regular action, and idempotentedness of `B`. It uses no supplied left `A`-action and no idempotentedness of `A`. `rightIOfNondegenerate` accepts `IsNondegenerateBimodule B A B` for precisely the selected actions and returns the direct functor definitionally. The two direct specializations therefore do not identify independent supplied `A`-actions.

All definitional interface equalities are proved by reflexivity. The original-ring membership criteria and whole-map inclusion naturality reuse the corresponding general lemmas. The inherited additive instances reuse the actual general functor instances.

## Universes and checks

The ring universes `uA` and `uB` and variable-carrier universe `uM` are independent. Both specialization output carriers live in exactly `max uB uM`. Their unbundled maps also admit an independent target universe `uN`.

The `Checks` namespace in the same Lean file assigns each complete unapplied declaration to an explicit interface for the ambient action, actual part, whole map, functor, natural inclusion, nondegeneracy adapter, additivity and composite equality of each specialization. These 48 checks use arbitrary independent universes and complementary assignments `(uA,uB,uM) = (0,1,0)` and `(1,0,1)`; map checks use `(0,1,0,1)` and `(1,0,1,0)`. Each interface selects the appropriate regular source action explicitly.

The competing-structure checks use coinciding ring, fixed-source and target carriers, two ring structures, two target group structures, competing original actions and competing ambient Hom actions. Explicit instance arguments verify that both functors retain the chosen ring, original source action, regular action and target group/action, and that their output part retains the subgroup group and inherited module built from those exact data.

Subsingleton checks cover both a subsingleton source `B` and a subsingleton target `M` for each actual part. The regular integer checks construct a nondegenerate right-regular integer object and the actual identity Hom as an element of the part, prove that element nonzero by evaluation at `1`, and verify both residual scalar formulas, bundled subtype scalar formulas, identity-map values, whole inclusion components and inclusion values.

The separate `NondegenerateRightHomFunctorChecks` unit supplies the general meaningful degenerate case with nonzero integer carriers, zero original actions, a nonzero identity Hom, zero entire residual action and trivial actual part, together with its subtype and inclusion formulas.

## Scope

These are the additive Hom functors and their actual nondegenerate output parts. The source I.4.2 comparison theorem is formulated for complex algebras; this internal construction establishes no recovered coefficient equalities or coefficient linearity. The intended coefficient compatibility in that source remains a separate question. Tensor-dual comparison maps, inverse identities, natural isomorphisms, adjunctions and exactness also remain separate obligations. This unit preserves the existing residual coefficient adapter constructions and their ownership.
