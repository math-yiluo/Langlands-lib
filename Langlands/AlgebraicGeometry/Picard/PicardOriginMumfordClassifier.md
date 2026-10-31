# The Mumford classifier and the origin dimension bound, conditional on two stalk-dimension facts

This module builds the morphism from an abelian variety `A` to a universal rigidified
Picard parameter `P` that classifies the Mumford family of a line bundle `L`. It then
proves the local-dimension bound
`Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u}`
*conditionally* on two generic statements, each passed in as a hypothesis:

```lean
theorem algClosedFieldRigidifiedPicardOriginDimensionLowerBound_of_stalkDimension
    (hq : QuasiFiniteAtStalkDimensionStatement.{u})
    (hs : FieldSmoothClosedPointStalkDimensionStatement.{u}) :
    AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u}
```

Here `Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionStatement` says that a
locally finite type morphism that is quasi-finite at `x` satisfies
`dim O_{X,x} ≤ dim O_{Y,f x}`. `Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement`
says that, at a closed point of a scheme smooth of relative dimension `g` over a field,
the stalk has Krull dimension `g`. Both are published statements with separately
published proofs. This module imports only the two statements: it proves neither and does
not assume either one globally. The unconditional proof is the separate module
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundProof`,
which applies this theorem to the two published proofs.

All auxiliary declarations live in the namespace
`Langlands.AbelianScheme.PicardOriginDimension`. The only global hypotheses are a field `k`
(algebraically closed from `isClosed_origin` on) and an abelian scheme `A` over
`S = Spec k`. Inside the namespace, `P`, `U` and `hU` are an arbitrary parameter over `S`, a
rigidified family on it and its all-test universality. Inspection of the conditional
theorem reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
the file uses no `sorry`.

## Imports

- the target statement module (unchanged);
- `MumfordUnit`, for `mumfordBundle` (the actual rigidified Mumford family built from a
  rigidified `L`, a chosen tensor inverse `M` and an evaluation `L ⊗ M ≅ O`) and
  `mumfordZeroParameterIso` (its restriction along the unit section `1 : T ⟶ A`
  is trivial as a rigidified family);
- `FieldMumfordPointComparisonProof`, for `FieldMumfordPoint.carrierIso`: the
  underlying module of the Mumford family, pulled back along a field-valued point `a`,
  is `t_x^*(i^*L) ⊗ i^*M` read through a symmetry. Here `x` is the corresponding point of
  the base change, `i` is the projection and `t_x` is translation by `x`;
- `TranslationInvarianceOfSmoothFamily`, for
  `TranslationOfSmoothFamily.pullback_iso_of_tensor_trivial`: if `t^*(s^*N) ⊗ s^*N'` is
  trivial for a tensor inverse `N'` of `N`, then `t^*L ≅ L` for every `L ≅ s^*N`. It is
  also used, through its imports, for `GroupScheme.fibreTranslationIso`,
  `GroupScheme.baseChangeSection`, `GroupScheme.baseChangePointsEquiv`,
  `LineBundle.isoOfPullbackIso` and the universal-family API
  (`RigidifiedLineBundle.classifyFamily`, `classifyFamily_pullback`,
  `classifyFamily_trivial`, `classifyFamily_eq_of_iso`, `isoOfClassifyFamilyEq`,
  `trivialParameter`);
- `LineBundleDualEvaluation`, for `LineBundle.exists_tensorObj_iso_structureSheaf`
  (every actual line bundle has a tensor inverse);
- `Modules.PullbackTensorProof`, for `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`
  (the pullback–tensor comparison is an isomorphism), the `preservation` argument of the
  Mumford constructions;
- the two generic statement modules `QuasiFiniteAtStalkDimensionStatement` and
  `FieldSmoothClosedPointStalkDimensionStatement` (statements only);
- Mathlib `AlgebraicGeometry.AlgClosed.Basic` (closed points of a locally finite type
  scheme over an algebraically closed field are rational points: `pointEquivClosedPoint`,
  `pointOfClosedPoint`, `ext_of_apply_closedPoint_eq`) and `AlgebraicGeometry.Fiber`
  (`Scheme.Hom.fiberHomeo`, `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`).

## The classifier

1. `unitRigidified k A L` rigidifies the actual bundle `L` along the unit section. Over a
   field, `fieldLineBundleTriviality` trivializes the restriction `e^*L`, and
   `RigidifiedLineBundle.ofLineBundle` uses the inverse of that trivialization. The
   carrier is still `L`; no normalization is applied.
2. `inverse L` and `inverseEvaluation L` are a chosen tensor inverse of `L` and its
   evaluation isomorphism, taken from `LineBundle.exists_tensorObj_iso_structureSheaf`.
3. `family k A L` is `mumfordBundle` applied to these data: a rigidified family on `A`
   parametrized by `A` itself.
4. `classifier k A U hU L : A.X ⟶ P` is
   `RigidifiedLineBundle.classifyFamily … U hU (family k A L)`, the morphism given by
   universality.

`one_comp_classifier` shows that the unit section composed with the classifier is
`trivialParameter`. By `classifyFamily_pullback` it classifies the pullback of the family
along `1`. That pullback is isomorphic to the trivial family by `mumfordZeroParameterIso`
(so `classifyFamily_eq_of_iso` applies), and `classifyFamily_trivial` finishes.
`classifier_unit` evaluates this at the closed point of `Spec k`: the classifier sends the
rational origin of `A` to `fullPicardOriginPoint k A U hU`.

## The stabilizer lemma

`baseChangeSection_left_fst` says that for a rational section `σ`, the base-changed
section `GroupScheme.baseChangeSection (𝟙 S) A.toGrp σ` followed by the projection
`pullback.fst A.X.hom (𝟙 S)` is `σ.left`. It is obtained from
`baseChangePointsEquiv.apply_symm_apply`.

`translation_iso_of_comp_classifier` proves: if `σ ≫ classifier = trivialParameter`, then
`(translation σ)^*L ≅ L`. The proof runs as follows.

- By `classifyFamily_pullback` and `classifyFamily_trivial`, the relative pullback of
  `family k A L` along `σ` and the trivial family over `Over.mk (𝟙 S)` have the same
  classifying morphism. `isoOfClassifyFamilyEq` gives a rigidified isomorphism `e₁`
  between them, and forgetting the rigidification gives an isomorphism `c₀` of module
  sheaves.
- Let `x` be the base-changed section of `σ`, `i = pullback.fst A.X.hom (𝟙 S)`,
  `t = (translation x).left`, `sy` the pullback symmetry and
  `E = t^*(i^*L) ⊗ i^*(inverse L)`. `FieldMumfordPoint.carrierIso` is applied with
  `b = 𝟙 S`, `Qc = sy.hom^*E`, the canonical identification `sy.inv^*(sy.hom^*E) ≅ E` as
  premise and the field triviality of `σ^*(inverse L)`. It identifies the carrier of the
  pulled-back Mumford family with `sy.hom^*E`. Combining it with `c₀` and pulling back
  along `sy.inv` gives `E ≅ O`.
- `TranslationOfSmoothFamily.pullback_iso_of_tensor_trivial` (with `s = i`,
  `N = L`, `N' = inverse L`) turns this into `t^*(i^*L) ≅ i^*L`.
- `GroupScheme.fibreTranslationIso` rewrites `t^*(i^*L)` as
  `i^*((translation σ)^*L)`. Since `i` is an isomorphism, `LineBundle.isoOfPullbackIso`
  descends the result to `(translation σ)^*L ≅ L`.

The lemma uses `set_option backward.isDefEq.respectTransparency false` (and its `.types`
variant) so that the base-change terms elaborate. These options affect only elaboration.

## Topology of the fibre

- `quasiFiniteAt_of_finite_fiber` is generic: if `f` is locally of finite type and the
  fibre `f ⁻¹' {f x}` is a finite set of closed points, then `f.QuasiFiniteAt x`. Via
  `quasiFiniteAt_iff_isOpen_singleton_asFiber` and the homeomorphism `fiberHomeo`, this
  reduces to `{x}` being open in the fibre. Its complement is the preimage of the finite
  union of the other closed singletons, which is closed.
- `isClosed_origin` (for locally finite type `P`) and `isClosed_unit` use
  `pointEquivClosedPoint`: the images of the rational sections `trivialParameter` and the
  unit section are closed points.
- `fiber_finite_and_closed` assumes the exact finite-stabilizer premise of the target and
  sets `Z = classifier ⁻¹' {origin}`, which is closed. A closed point `z` of `Z` gives a
  rational section `pointOfClosedPoint` of `A`. Its composite with the classifier agrees
  with `trivialParameter` at the closed point of `Spec k`, so the two are equal by
  `ext_of_apply_closedPoint_eq` (applied to the locally finite type `P`). The stabilizer
  lemma then puts the section in the stabilizer. This map is injective, so
  `Z ∩ closedPoints` is finite and therefore closed. `A` is locally of finite type over a
  field, hence a Jacobson space, and `JacobsonSpace.closure_inter_closedPoints_eq_closure`
  gives `Z ∩ closedPoints = Z`. So `Z` is a finite set of closed points.
- `locallyOfFiniteType_classifier`: `classifier ≫ P.hom = A.X.hom` is locally of finite
  type, so the classifier is too (`locallyOfFiniteType_of_comp`).
- `quasiFiniteAt_classifier` combines the previous items with `classifier_unit`: the
  classifier is quasi-finite at the rational origin of `A`.

## The conditional assembly

Given the binders of the target (`k`, `A`, `P`, `U`, `hU`, `g`, `LocallyOfFiniteType P.hom`,
`hA : A.HasRelativeDimension g`, `L` and the finite-stabilizer premise), the proof does
the following.

- `hs` applied to `A.X.hom`, which is `SmoothOfRelativeDimension g` by `hA` (an `abbrev`),
  and the closed origin (`isClosed_unit`) rewrites `g` as the Krull dimension of the stalk
  of `A` at the origin.
- `classifier_unit` rewrites the origin point of `P` as the classifier's image of the origin
  of `A`.
- `hq` applied to the classifier (`locallyOfFiniteType_classifier`,
  `quasiFiniteAt_classifier`) gives the inequality.

No hypothesis beyond those of the target and the two named statements is used. The
finite-stabilizer premise enters only through `quasiFiniteAt_classifier`. This
module asserts no existence of an ample bundle or of a bundle with finite stabilizer.
