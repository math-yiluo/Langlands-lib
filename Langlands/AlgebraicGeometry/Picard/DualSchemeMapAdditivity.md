# Additivity of the dual scheme maps

Module `Langlands.AlgebraicGeometry.Picard.DualSchemeMapAdditivity` proves that
dualization carries a sum of homomorphisms of abelian schemes to the product
of the dual maps under the constructed tensor multiplication on the chosen
dual. The argument works over an arbitrary base `S`. The theorem
`fieldDualSchemeMapAdditivity_of_classification` specializes it to the target
statement `Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`.

The results are conditional. The general lemmas and the final theorem take
two explicit hypotheses: `classification`, a proof of
`PicardZeroLineBundleClassificationStatement`, and `globalFunctions`, a proof
of `Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions`. The
target statement itself quantifies over
`preservation : pullbackTensorComparisonIsIsoStatement`,
`stability : PicardZeroPullbackStatement` and the chosen duals
`hA hB : HasDualScheme _`. This module proves none of the four propositions
`PicardZeroLineBundleClassificationStatement`,
`SmoothProperConnectedGlobalFunctions`, `pullbackTensorComparisonIsIsoStatement`
and `PicardZeroPullbackStatement`.

The two hypotheses are proved elsewhere in the Library, as
`Langlands.AbelianScheme.picardZeroLineBundleClassification` and
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`. The
separate module `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityProof`
passes them to `fieldDualSchemeMapAdditivity_of_classification` and so proves
the target as `Langlands.AbelianScheme.fieldDualSchemeMapAdditivity`. Like the
target, that theorem keeps `preservation`, `stability`, `hA` and `hB` as
arguments. Similarly, `Langlands.AbelianScheme.relativeDualSchemeMapAdditivity`
passes the two proofs to `dualSchemeMap_add`. The homomorphism-pullback input
is the published `homPicardZeroPullback`.

## Tensor compatibility of pullback (`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle`)

* `classesPullback_tensor_of_retraction preservation f ε section_eq h q r`:
  for `h : T ⟶ U` in `Over S`, relative pullback of rigidified classes along
  `h` preserves `classesTensor`. Each relative family has the projection
  `T ×_S X ⟶ T` as a retraction of its section. So
  `RigidifiedLineBundle.isoOfCarrierIso` (module `RigidifiedCarrierIso`) turns
  the Library tensor comparison isomorphism `pullbackTensorComparison` of the
  underlying bundles into an isomorphism of rigidified bundles. No coherence of
  the comparison with rigidifications is used. This replaces the Library route
  through `pullbackTensorCompositionStatement`. Its only proof module,
  `Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs`,
  cannot be imported together with the target statement module.

## Dual tensor (`Langlands.AbelianScheme`)

* `picardZeroClassesPullback_tensor_of_preservation`: the same compatibility
  for Picard-zero classes.
* `dualTensor_points_of_preservation`: for `f g : T ⟶ dualScheme A hA`, the
  class classified by `prod.lift f g ≫ dualTensor stability A hA preservation`
  is the tensor of the classes classified by `f` and `g`.
* `dualClassify_tensor_of_preservation`: `dualClassify` of a tensor of two
  Picard-zero classes is `prod.lift` of the two classifying maps followed by
  `dualTensor`. It follows from the previous lemma by
  `dualPointClass_injective` and `dualPointClass_classify`.

## Homomorphisms

* `homFamilySpaceMap_app_eq f T`: the Library map
  `(homFamilySpaceMap f).app T : T ×_S A ⟶ T ×_S B` is the point
  `pairOver B (relativeFst A T) (relativeSnd A T ≫ (groupHom f).hom.hom)`
  (definitional).
* `relativeSnd_comp_add f g T`: the composite of the projection to `A` with
  `f + g` is the product of the composites with `f` and with `g`, in the group
  of points of `B`.
* `homPicardZeroClassesPullback_add preservation classification stability globalFunctions hB f g T q`:
  pulling a Picard-zero class `q` on `T ×_S B` back along `f + g` gives the
  tensor of its pullbacks along `f` and along `g`. For a representative `L`,
  `nonempty_pullback_pairOver_mul_iso` (module `SquareTheorem`) gives the
  isomorphism of underlying bundles
  `(pr_T, (f + g) ∘ pr_A)^* L ≅ (pr_T, f ∘ pr_A)^* L ⊗ (pr_T, g ∘ pr_A)^* L`.
  `RigidifiedLineBundle.nonempty_iso_of_forget_iso` upgrades it to an
  isomorphism of rigidified bundles.

## Main theorems

* `dualSchemeMap_add preservation classification stability globalFunctions hA hB f g`:
  over an arbitrary base `S`, for abelian schemes `A`, `B` with
  `HasDualScheme` and homomorphisms `f g : A ⟶ B`,

  `dualSchemeMap homPicardZeroPullback (f + g) hA hB =
    prod.lift (dualSchemeMap homPicardZeroPullback f hA hB)
      (dualSchemeMap homPicardZeroPullback g hA hB) ≫ dualTensor stability A hA preservation`.

  The dual map is `dualClassify` of the pullback of the Poincaré class of `B`.
  The equation is `dualClassify_tensor_of_preservation` applied to the two
  pullbacks, rewritten by `homPicardZeroClassesPullback_add`.
* `fieldDualSchemeMapAdditivity_of_classification classification globalFunctions :
  FieldDualSchemeMapAdditivityStatement.{u}`: the target statement, obtained by
  specializing `dualSchemeMap_add` to `S = Spec k`.

## Provenance

This is the additivity of dualization of homomorphisms,
`(f + g)^∨ = f^∨ + g^∨`. Compare Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (registered `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
printed page = PDF page − 4), Chapter VII, Corollary (7.17), printed p.104
(PDF p.108): over a field, `f ↦ f^t` is a homomorphism
`Hom(X, Y) → Hom(Y^t, X^t)`. The source deduces it from Lemma (7.16)(i) on
the same page. Over a field `k`, for a line bundle `L` on `X_T` with `ϕ_L = 0`
and morphisms `f, g : Y → X_T` over `T`, it states
`[(f + g)^* L] = [f^* L ⊗ g^* L]` in `Pic_{Y/T}(T)`. The Lean proof uses the
rigidified Picard-zero analogue of this lemma over an arbitrary base,
`nonempty_pullback_pairOver_mul_iso` from `SquareTheorem`. That module proves
it by the classification-and-rigidity argument of `ShearClassification`, not
by the source's route through Lemma (7.15) and the theorem of the cube.
