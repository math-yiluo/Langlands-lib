# Transition functions of pulled-back frames on the test covers

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Transitions`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

The notation follows `OpennessOfVersality.CechData` and `OpennessOfVersality.Obstruction`:
`f : X ⟶ Spec R`, an `R`-algebra `P` with an ordered affine cover `K` of
`relSpace f P`, a `P`-algebra `A` with the pulled-back cover `testCover f K A` (opens
`relMap f (P → A)⁻¹ K.U i`), and `pr` (restriction of pairwise data to finite
intersections). Transition functions follow the Library convention `IsTransition e g`:
`e j = g i j • e i` on `T i ⊓ T j`.

## Declarations

- `pair_le`, `pairMapAlong s hs i j`, `pairUnitsAlong s hs g`: for an `R`-algebra map
  `s : P →ₐ[R] A` with the same preimages as the structure map (`hs`), the section map
  `Γ(relSpace f P, K.U i ⊓ K.U j) ⟶ Γ(relSpace f A, T.U i ⊓ T.U j)` (`appLE` of
  `relMap f s`), and the image of a family of units `g`.
- `pr_pairMapAlong`, `pr_pairUnitsAlong_val`, `pr_pairUnitsAlong_inv`: restricting the
  pushed pairwise data to `T.inter σ` gives `secMapAlong s σ` of the restricted data
  (`Scheme.Hom.appLE_map`, `Scheme.Hom.map_appLE`).
- `testCover_le_preimage`: `T.U i ≤ relMap f χ⁻¹ (testCover f K A₀).U i` for an
  `R`-algebra map `χ : A₀ →ₐ[R] A` with `χ ∘ (P → A₀)` having the structure preimages.
- `isTransition_pullback_res`: if frames `e` on `testCover f K A₀` have transition
  functions `pairUnitsAlong (P → A₀) g`, then their pullbacks along `relMap f χ`,
  restricted to `T.U i`, have transition functions
  `pairUnitsAlong (χ ∘ (P → A₀)) g`. The proof applies `LineHom.isTransition_pullback`
  and restricts.
- `pushUnits w W hW g`: the family `g` pushed along an arbitrary morphism
  `w : Y ⟶ relSpace f P` to opens `W i` of `Y` with
  `W i ⊓ W j ≤ w⁻¹ (K.U i ⊓ K.U j)`. `pushUnits_congr`: equal morphisms give equal
  families. `pairUnitsAlong s hs g` is `pushUnits (relMap f s) T.U _ g` by definition.
- `isTransition_pullback_push`: let frames `e` on opens `T` have transitions
  `pushUnits w T _ g`. Pull them back along `v : Y ⟶ Z'` and restrict them to opens
  `W i ≤ v⁻¹ T i`. The resulting frames have transitions `pushUnits (v ≫ w) W _ g`.
- `isTransition_map`: a morphism of module sheaves preserves transition relations.

## Provenance

Internal infrastructure for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It is built from
the Library's `Picard/CocycleLineBundleFrame`, `Picard/CocycleLineBundlePullback` and
`Picard/LineHom/TestCoordinates`. No literature statement is formalized.
