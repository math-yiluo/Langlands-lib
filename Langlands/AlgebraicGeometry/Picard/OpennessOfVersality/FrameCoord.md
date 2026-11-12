# Frame coordinates of morphisms between pullbacks to a common scheme

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.FrameCoord`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

Setting: schemes `Z, Z', A, B`, module sheaves `C` on `A` and `D` on `B`, and maps
`u : Z ⟶ A`, `v : Z ⟶ B`. Sections are pulled back with the ported FLT
`Scheme.Modules.pullbackLocalSection` (`pbs` below). `res_h` denotes the restriction map
of a module sheaf along `h : W ≤ V`.

## Declarations

- `app_res`: a morphism of module sheaves commutes with restriction,
  `φ.app W (res_h s) = res_h (φ.app V s)`.
- `res_res`: restricting twice is restricting along the composite inclusion.
- `HasCoord φ e f hu hv a`, for `φ : u^* C ⟶ v^* D`, sections `e ∈ Γ(C, T)` and
  `f ∈ Γ(D, T')`, an open `W` of `Z` with `hu : W ≤ u⁻¹ T`, `hv : W ≤ v⁻¹ T'`, and
  `a ∈ Γ(Z, W)`, means `φ.app W (res_hu (pbs u e)) = a • res_hv (pbs v f)`. That is, on
  `W` the morphism sends the pulled-back section `e` to `a` times the pulled-back
  section `f`.
- `HasCoord.tr`: for `k : Z' ⟶ Z` with `k ≫ u = u'`, `k ≫ v = v'`, and an open
  `W' ≤ k⁻¹ W` (with `W' ≤ u'⁻¹ T`, `W' ≤ v'⁻¹ T'`), the transported morphism
  `LineBundleFlatDescent.tr k _ _ φ : u'^* C ⟶ v'^* D` has coordinate
  `k.appLE W W' _ a`. The proof writes `tr` with Mathlib's composition comparisons
  (`compIso_rfl`). It then uses `LineHom.pullbackComp_inv_app_pullbackLocalSection`, the
  FLT lemmas `map_homOfLE_pullbackLocalSection`, `pullbackLocalSection_app` and
  `pullbackLocalSection_smul`, and the Library's `sectionPullback_comp`.
- `HasCoord.mono` (restriction to a smaller open restricts the coordinate) and
  `HasCoord.comp` (coordinates of a composite multiply).
- `HasCoord.unique`, `HasCoord.exists`: if `f` is a frame on `T'` (FLT
  `IsFrameOn`), the coordinate exists and is unique. The pulled-back frame is a frame
  (FLT `IsFrameOn.pullbackLocalSection`), and multiplication by it is bijective.
- `hom_ext_of_frames`: two morphisms `M ⟶ N` agree if both modules have frames on a
  common cover and the morphisms agree on the frames of `M`. Proof: injectivity of the
  Library's `LineHom.frameHomEquiv`, with the canonical transition functions
  `CocycleGluing.frameCocycle`.
- `exists_iso_of_gauge`: frames `s i` of `P₁` and `t i` of `P₂` on a cover, with
  transition functions `α`, `β`, and a gauge family of units `a`
  (`CocycleGluing.IsGaugeFamily α β a`), give an isomorphism `ψ : P₁ ≅ P₂` with
  `ψ.hom.app (T i) (s i) = a i • t i`. The morphism is `(frameHomEquiv …).symm ⟨a, _⟩`.
  It is an isomorphism by the FLT criterion `Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top`,
  since a unit multiple of a frame is a frame (`DualNumberThickening.isFrameOn_smul_unit`).
- `tr_eq_of_hasCoord`: let `ψ : u^* C ⟶ v^* D` have coordinates `a i` on opens `W i`
  with respect to frames `e i` of `C` and `fr i` of `D`. Let
  `φ : u'^* C ⟶ v'^* D` have coordinate `1` on opens `W' i` covering `Z'`. If
  `k.appLE (W i) (W' i) _ (a i) = 1`, then `tr k _ _ ψ = φ`. Proof: `hom_ext_of_frames`
  with the restricted pulled-back frames on `W' i`, and `HasCoord.tr`.

## Provenance

Internal infrastructure for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It is built from
the ported FLT pullback of local sections and frames, the Library modules
`Picard/LineHom/TestCoordinates`, `Picard/LineHom/FrameHom`,
`Picard/CocycleLineBundleFrame` and `Modules/LineBundleFlatDescentStr`, and Mathlib's
module pullbacks. No literature statement is formalized.
