# Proof: flat base change for higher direct images

The theorem
`Langlands.AlgebraicGeometry.Modules.flatHigherDirectImageBaseChange`
proves the entire published proposition
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement.{u}`,
in arbitrary universe `u`, with no outer parameters or extra hypotheses.

For schemes `X Y X' Y'`, morphisms `f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'`,
`g' : X' ⟶ X` with `IsPullback g' f' f g`, `f` quasi-compact and separated,
`g` flat, a quasi-coherent `M : X.Modules` and every `n : ℕ` (including `0`),
it gives an isomorphism
`(Scheme.Modules.pullback g).obj ((DerivedSections.higherDirectImage f n).obj M) ≅
  (DerivedSections.higherDirectImage f' n).obj ((Scheme.Modules.pullback g').obj M)`.

## Implemented proof

The isomorphism is the component at `M` of the published base change
transformation `DerivedSections.higherDirectImageBaseChangeNatTrans g f f' g' h.w n`
(module `Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange`),
which is defined when pullbacks along `g` and `g'` preserve finite limits.

1. `g'` is flat as a base change of the flat `g`
   (Mathlib's `MorphismProperty.of_isPullback` applied to `h.flip`).
2. Pullbacks along `g` and `g'` preserve finite limits by the published
   theorem `flatPullbackExact` (Stacks Project, tag 02N4).
3. The component is an isomorphism by
   `FlatBaseChange.isIso_higherDirectImageBaseChange` (module
   `FlatBaseChange.Gluing`), and `asIso` of the component is the required
   isomorphism.

So the isomorphism is not merely shown to exist: it is the canonical base
change map `g^* Rⁿ f_* M ⟶ Rⁿ f'_* g'^* M`.

## Helper modules

All in namespace `Langlands.AlgebraicGeometry.Modules.FlatBaseChange`, except
`Cohomology.ExactBaseChange.ResolutionMap`, which is in `Langlands.Cohomology.ExactBaseChange`.
Each has its own Markdown file with the full argument.

- `Cohomology.ExactBaseChange.ResolutionMap`: the cochain map `resolutionBaseChangeMap` and the
  criterion `isIso_map_baseChangeNatTrans_app_iff` (invertibility of a component
  of the base change transformation, after any functor, is invertibility of
  the homology of that cochain map), from the published
  `resolutionCompatibility`.
- `FlatBaseChange.AffineCase`: the case `g = Spec.map φ` for a ring map `φ`,
  through the sheafified Čech resolutions of a finite ordered affine cover,
  the published `cechTermDirectImage` and the published
  `pushforwardBaseChangeOfIso`.
- `FlatBaseChange.OpenImmersionCase`: the case of an open immersion on the
  base, for every module, through an injective resolution and its flasque
  restriction.
- `FlatBaseChange.Composition`: transfer of invertibility across horizontally
  pasted squares.
- `FlatBaseChange.Gluing`: the affine-local criterion and the assembly of the
  three cases.

## Dependencies

Only accepted, published and proved Library results are used. The published
proofs of Library propositions used directly are

- `Langlands.Cohomology.ExactBaseChange.resolutionCompatibility`
  (module `Langlands.Cohomology.ExactBaseChange.ResolutionProof`);
- `Langlands.Cohomology.acyclicResolutionComparisonStatement`
  (module `Langlands.Cohomology.AcyclicResolution.ComparisonProof`);
- `Langlands.AlgebraicGeometry.Modules.CechResolution.cechTermDirectImage`
  (module `Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageProof`);
- `Langlands.AlgebraicGeometry.Modules.DerivedSections.pushforwardBaseChangeOfIso`
  (module `Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeOfIsoProof`);
- `Langlands.AlgebraicGeometry.Modules.flatPullbackExact`
  (module `Langlands.AlgebraicGeometry.Modules.FlatPullbackExactProof`).

They are used together with the published definitions
`higherDirectImageBaseChangeNatTrans`, `pushforwardBaseChangeNatTrans`,
`pushforwardBaseChangeOf` and the Čech complexes `cechComplex`, `cechAug`,
`cechPullback`, and with published lemmas of the Library modules on Čech
resolutions (`quasiIso_cechAug`, `cechAug_cechPullback`,
`isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated`), degree-zero base
change (`isIso_pushforwardBaseChange_of_isOpenImmersion`,
`pushforwardBaseChange_composition`,
`pushforwardBaseChange_comp_pushforward_map`), flasque vanishing
(`PushforwardInjectiveAcyclic.isFlasque_of_injective`,
`isZero_higherDirectImage_of_isFlasque`), affine-local detection of
isomorphisms (`isIso_of_affineOpenPullbacks`,
`exists_affineOpenFactorization`) and resolution comparisons
(`AcyclicResolution.lift`, `quasiIso_mapResolutionAugmentation`,
`LeftExactHomology.homologyNatTrans`). No published statement is used as a
hypothesis. Neither Mumford Euler statement
(`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`,
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`), nor any
module importing them, nor any consequence of this target is in the import
closure.

## Source

The Stacks Project, Cohomology of Schemes, Lemma 30.5.2 (tag 02KH), existence
part, restricted to quasi-compact separated `f` (registered source
`stacks-flat-base-change-projection-formula-2026-11-02`). As in the source, a
global comparison map is constructed first and shown to be invertible on an
affine open cover of the base. In the affine case the source computes
cohomology with a Čech complex of a finite affine cover and uses exactness of
`- ⊗_R R'`. The Lean proof instead uses the sheafified Čech resolution: its
terms have isomorphic degree-zero base change maps without any flatness, and
flatness enters only through the exactness of the pullbacks `g^*` and `g'^*`
(`flatPullbackExact`), which lets them commute with cohomology. The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
