# Extension of generic two-axis-trivial bundles over normal finite-type integer domains

Module `Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionProof`
proves

```lean
theorem Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty :
    NormalFiniteTypeTwoAxisExtensionProperty.{u}
```

for an arbitrary universe `u`, with no hypotheses. The statement
`Langlands.AbelianScheme.NormalFiniteTypeTwoAxisExtensionProperty` is defined in
module `Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionReduction`.

Let `T : Type u` be an integrally closed domain of finite type over `ℤ` and
`B` an actual Library abelian scheme over `Spec T`. Let
`b = Spec.map (algebraMap T (FractionRing T))` and let `G` be the base change of
`B` along `b`. Let `N` be an actual line bundle on `mumfordProduct G` whose
module-sheaf pullbacks to both unit axes are isomorphic to the structure sheaf.
Then the theorem gives an actual line bundle `E` on `mumfordProduct B` and an
actual module-sheaf isomorphism from the pullback of `E` along
`mumfordProductBaseChangeMap B b` to `N`. The theorem adds no polarization,
dual scheme, projectivity, regularity or dimension hypothesis. It does not
extend the chosen axis trivializations.

## Proof

The proof is one term that combines published Library results in four steps.

1. **Murre's criterion.**
   `Langlands.AlgebraicGeometry.UnramifiedFunctor.murreCriterion.{u, u + 1}`
   (module `UnramifiedFunctor.MurreCriterion`) proves
   `MurreCriterionStatement.{u, u + 1}`. This is Murre's criterion for
   presheaves on `Over S` with values in `Type (u + 1)`, over a locally
   noetherian `S : Scheme.{u}`.
2. **The ten Murre conditions for the two-axis class presheaf.** The following
   theorems in namespace `Langlands.AlgebraicGeometry.Picard` prove the ten
   statements of `TwoAxisClassMurreConditionsStatement` for
   `TwoAxisRigidifiedLineBundle.classPresheaf A`, for every abelian scheme `A`
   over the spectrum of a noetherian ring in `Type u`:
   - `noetherianTwoAxisClassSmallValues` (`TwoAxisClassSmallValuesProof`);
   - `noetherianTwoAxisClassZariskiSheaf` (F1a, `TwoAxisClassZariskiSheafProof`);
   - `noetherianTwoAxisClassFaithfullyFlatSheaf` (F1b,
     `TwoAxisClassFaithfullyFlatSheafProof`);
   - `noetherianTwoAxisClassFilteredColimits` (F2,
     `TwoAxisClassFilteredColimitsProof`);
   - `noetherianTwoAxisClassAdicLimits` (F3, `TwoAxisClassAdicLimitsProof`);
   - `noetherianTwoAxisClassArtinianLifting` (F4′,
     `TwoAxisClassArtinianLiftingProof`);
   - `noetherianTwoAxisClassNilpotentInjective` (strong F5,
     `TwoAxisClassNilpotentInjectiveProof`);
   - `noetherianTwoAxisClassValuativeSeparation` (F6,
     `TwoAxisClassValuativeSeparationProof`);
   - `noetherianTwoAxisClassOneDimensionalLifting` (F7,
     `TwoAxisClassOneDimensionalLiftingProof`);
   - `noetherianTwoAxisClassGenericNonLifting` (F8,
     `TwoAxisClassGenericNonLiftingProof`).
3. **Representability.** `noetherianTwoAxisClassRepresentability_of_murre`
   (module `TwoAxisClassMurreReduction`) takes the theorem from step 1 and the
   ten theorems from step 2 in this order. It returns
   `NoetherianTwoAxisClassRepresentabilityStatement.{u}`. For every noetherian
   ring `R` in `Type u` and abelian scheme `A` over `Spec R`, the class presheaf
   of `A` is then represented by some `q : Y ⟶ Spec R` that is separated,
   locally of finite type and formally unramified.
4. **Extension.**
   `Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability`
   (module `TwoAxisClassRepresentabilityReduction`) turns this representability
   into `NormalFiniteTypeTwoAxisExtensionProperty.{u}`. `T` is noetherian
   because it is of finite type over `ℤ`. The representing scheme of the class
   presheaf of `B` satisfies discrete valuative existence
   (`discreteValuativeExistence_of_representableBy`). Since `T` is normal,
   `actualBundleExtension_of_normal_discreteValuativeExistence` then extends
   the generic class and gives an actual bundle `E` with the required
   restriction isomorphism along the canonical map.

## Dependencies and axioms

No Lean file in the import closure names any of the declarations that the task
excludes: `NormalFiniteTypeAbelianAmpleExistenceStatement`,
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` and
`SmoothFamilyAbelianRepresentabilityStatement`. So the proof uses neither
these statements nor their proofs. The closure also names none of the targets of
the paused allocations: `RelativeDualSchemeExistenceStatement`,
`FieldDualSchemeExistenceStatement`,
`FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement` (or its proof) and
`FiniteTypePicardStackAtlasStatement`. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Source

Steps 1–3 follow the reduction in the proof of Raynaud, LNM 119,
Theorem III 4.4. Raynaud reduces to a noetherian affine base. He then obtains
the representability of the functor of rigidified classes from Murre's
Theorem 4 (Séminaire Bourbaki exp. 294), whose proof checks the conditions of
Murre's Theorem 1. The precise locators are in the paired Markdown of
`TwoAxisClassMurreReduction`, `MurreCriterionStatement` and
`TwoAxisClassMurreConditionsStatement`. Step 4 composes Library results
internally, as explained in the paired Markdown of
`TwoAxisClassRepresentabilityReduction`.
