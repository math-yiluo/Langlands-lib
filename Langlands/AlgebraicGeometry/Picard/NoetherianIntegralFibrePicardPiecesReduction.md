# Proof of the reduction of the noetherian-test Picard scheme to its pieces

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardPiecesReduction`
proves

```lean
theorem noetherianIntegralFibrePicardPiecesReduction :
    NoetherianIntegralFibrePicardPiecesReductionStatement.{u}
```

So the noetherian-test Picard statement
`NoetherianIntegralFibrePicardNoetherianTestsStatement` follows from five hypotheses:
`ProperAmpleClosedImmersionBySectionsStatement` (K1),
`PicardHilbertPolynomialPiecesStatement` (the pieces),
`PicardHilbertPiecesRepresentabilityStatement` (representability of each piece),
`ProperFlatIntegralSheafClassTwistStatement` (classes and twists) and
`NoetherianOpenPiecesGluingStatement` (gluing). The proof proves none of the five; it only
assembles them, following the proof of Kleiman's Theorem 4.8 (see the statement's Markdown).

## Two auxiliary lemmas

- `isSheaf_zariskiTopology_over_of_fppf`: a type-valued presheaf on `Over S` that is a sheaf
  for `Scheme.fppfTopology.over S` is a sheaf for `Scheme.zariskiTopology.over S`. Mathlib's
  `Scheme.zariskiPrecoverage_le_fppfPrecoverage` and `Precoverage.toGrothendieck_mono` give
  `zariskiTopology ≤ fppfTopology`. A sieve on `Y : Over S` covers in `J.over S` exactly when
  its image on `Y.left` covers in `J`, which is definitional (`mem_over_iff`), so the
  inequality passes to the topologies on `Over S`. `Presheaf.IsSheaf.of_le` concludes.
- `relativeSpaceSymmetry_inv_map`: for `h : T' ⟶ T` in `Over S`,

  ```lean
  (relativeSpaceSymmetry f T').inv ≫ (relativeSpace f).map h =
    pullback.map f T'.hom f T.hom (𝟙 X) h.left (𝟙 S) _ _ ≫ (relativeSpaceSymmetry f T).inv
  ```

  as maps `X ×_S T' ⟶ T ×_S X`. It is checked on the two projections, using the naturality of
  `relativeProjection`, `relativeSpace_map_snd` and the `pullbackSymmetry` projection lemmas.

## The main proof

Fix `R`, `f : X ⟶ Spec R` and the hypotheses of the conclusion. Write `S = Spec R`.

1. **Embedding.** K1, applied to the properness of `f` and the ample line bundle, gives an
   invertible `𝓛X` with `ClosedImmersionBySections 𝓛X f`.
2. **Pieces.** The pieces statement, applied to `f` and `𝓛X`, gives `κ`, `θ`, `U` and its five
   properties P1–P5. The representability statement takes P1, P2, P4, P5 and the section, and
   gives for every `(c, m)` a scheme `Q c m` and a map `β c m` (chosen with `choose`).
3. **Classes.** `f` is locally of finite presentation: it is proper, hence locally of finite
   type, and `Spec R` is locally noetherian (Mathlib's instance). So the class/twist statement
   applies over every `T : Over S`. With `choose` it gives, for every element `ξ` of
   `RelativePicard.classSheafPresheaf f` at `T`, a line bundle `rep T ξ` on `T ×_S X` with
   `sheafClassOf f T (rep T ξ) = ξ`.
4. **Transport.** For a line bundle `L` on `T ×_S X`, set
   `tr T L = (Scheme.Modules.pullback (relativeSpaceSymmetry f T).inv).obj L.obj`, a module on
   `X ×_S T = pullback f T.hom`. It is invertible:
   `isInvertible_of_isLocallyFreeRankOne` turns the line bundle into an invertible module, and
   `Scheme.Modules.IsInvertible.pullback` preserves invertibility.
5. **The opens of the gluing statement.** Put `V T ξ c m = U T.left T.hom (tr T (rep T ξ)) c m`,
   with `F = RelativePicard.classSheafPresheaf f`.

The four hypotheses of the gluing statement are then checked on locally noetherian tests.

- **Zariski sheaf.** `isSheaf_zariskiTopology_over_of_fppf` applied to
  `RelativePicard.classSheafPresheaf_isSheaf f`.
- **Base change.** This uses three facts about `U` on locally noetherian `T`.
  - *Isomorphism invariance.* If `L ≅ L'` are invertible, then `U L = U L'`. Apply P1 with
    `N = 𝟙_` (invertible by `Scheme.Modules.isInvertible_unit`), using
    `L' ≅ L' ⊗ 𝟙_ ≅ L' ⊗ g^* 𝟙_` (`ρ_` and the FLT `pullbackTensorUnitObjIso`).
  - *Class invariance.* If `sheafClassOf L = sheafClassOf L'`, the class/twist statement gives
    an invertible `N` on `T` and `L.obj ≅ L'.obj ⊗ p^* N`, with `p = pullback.fst T.hom f` the
    projection. Pulling back along the symmetry, by the FLT `pullbackTensorObjIso`,
    `Scheme.Modules.pullbackComp` and `pullbackCongr`, gives
    `tr T L ≅ tr T L' ⊗ (pullback.snd f T.hom)^* N`. Then P1 gives `U (tr T L) = U (tr T L')`.
  - *Pullback.* For `h : T' ⟶ T`, P2 is stated for the structure map `h.left ≫ T.hom`, while
    `T'` carries `T'.hom`. The two are only propositionally equal (`Over.w h`), so P2 is first
    restated for an arbitrary `s'` with `h ≫ s = s'` and proved there by `subst`. The lemma
    `relativeSpaceSymmetry_inv_map` and `pullbackComp` give
    `tr T' (h^* L) ≅ h_X^* (tr T L)`, where `h_X` is the base-change map of P2. Isomorphism
    invariance and P2 then give `U (tr T' (h^* L)) = h.left ⁻¹ᵁ U (tr T L)`.

  For `ξ` at `T`, `map_sheafClassOf` shows that `rep T' (F.map h.op ξ)` and the pullback of
  `rep T ξ` have the same class. Class invariance and the pullback fact give
  `V T' (F.map h.op ξ) c m = h.left ⁻¹ᵁ V T ξ c m`.
- **Shape.** P3 applied to `tr T (rep T ξ)`.
- **Quasi-projectivity.** `IsHQuasiProjective (Q c m).hom` provides an immersion into
  `ProjectiveSpace R n` over `Spec R`; its quasi-compactness is dropped.
- **Representability.** Injectivity is the representability statement's. For the image,
  apply its criterion to `rep T ξ` and rewrite `sheafClassOf f T (rep T ξ) = ξ`.

The gluing statement then returns exactly the conclusion of
`NoetherianIntegralFibrePicardNoetherianTestsStatement` for `F = classSheafPresheaf f`.

## Notes

- The tensor products are those of the FLT port's monoidal structure on `Scheme.Modules`
  (from `Def_SheafOfModules_Monoidal`), the same instance used by the hypotheses. The pullback
  isomorphisms come from `Def_AlgebraicGeometry_ModulesPullbackMonoidal`.
- The proof uses no `sorry` and no axioms beyond Lean's standard ones.
