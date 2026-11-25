/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage

/-!
# The projection map of the right adjoint of the functor induced by an exact monoidal functor

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint,
and let `adj : D(F) ⊣ G` be an adjunction, where `D(F)` is the functor induced by `F` on derived
categories. For `E` in `D(D)` the projection map
`τ_E : G E ⊗ᴸ K ⟶ G (E ⊗ᴸ D(F) K)` (`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`)
is the transpose of the comparison `D(F)(G E ⊗ᴸ K) ⟶ D(F) G E ⊗ᴸ D(F) K` followed by the
counit of `adj`. We show:

- `CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_tensorUnit`: `τ_E` is an
  isomorphism at the unit;
- `CategoryTheory.Functor.commShift_mapDerivedCategoryProjectionMap`: `τ_E` commutes with the
  shifts, for the commutation of `G` with the shifts induced by the adjunction;
- `CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE`: if `G`
  does not lower the cohomological degree, `E` is bounded below and `τ_E` is an isomorphism at
  the flat objects placed in degree `0`, then `τ_E` is an isomorphism at every `K` of Tor
  amplitude in `[b, ∞)`. Such a `K` is represented by a K-flat complex `P` of flat objects
  vanishing below `b` whose image under `F` is K-flat; in a fixed degree `q`, both sides only
  depend on the stupid truncation `σ^{≤ N} P` for `N ≫ q`, which is a bounded complex of flat
  objects.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

omit [F.Monoidal] in
/-- An object of Tor amplitude in `[b, ∞)` is represented by a K-flat complex of flat objects
vanishing in degrees `< b` whose image under `F` is K-flat: the canonical truncation `τ^{≥ b}` of
a functorial flat resolution. -/
lemma exists_kFlat_model_of_torAmplitudeGE {b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeGE C b K) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE b), (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((F.mapHomologicalComplex _).obj P) ∧
      Nonempty (Q.obj P ≅ K) := by
  have (Y : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj Y) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
  have := isGE_of_torAmplitudeGE hK
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  let L := Q.objPreimage K
  let R := Λ.resolutionFunctor.obj L
  have hR : ∀ n, ObjectProperty.flat (R.X n) := fun n ↦ by
    have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj L
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) n) c.isColimit)
      (fun i ↦ ObjectProperty.flat.essImage_ι_le _ ((c.prop_diag_obj i).1 n))
  have hRk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
  have hFR := F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
    ObjectProperty.flat.essImage_ι_le L
  have : IsIso (Q.map (Λ.resolutionNatTrans.app L)) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  let e : Q.obj R ≅ K := asIso (Q.map (Λ.resolutionNatTrans.app L)) ≪≫ Q.objObjPreimageIso K
  have : R.IsGE b := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e.symm b
  have hex := exactAt_tensorRight_of_torAmplitudeGE R hRk
    ((torAmplitudeGE C b).prop_of_iso e.symm hK)
  exact ⟨R.truncGE b, inferInstance, R.flat_truncGE_X b hR hex, R.kFlat_truncGE b hR hRk hex,
    CochainComplex.kFlat_mapHomologicalComplex_obj_truncGE F R b hR hFR hex,
    ⟨(asIso (Q.map (R.πTruncGE b))).symm ≪≫ e⟩⟩

variable {F} {G : DerivedCategory D ⥤ DerivedCategory C} (adj : F.mapDerivedCategory ⊣ G)

/-- The projection map `G E ⊗ᴸ K ⟶ G (E ⊗ᴸ D(F) K)` for a fixed `E`, as a natural transformation
of functors of `K`: the transpose along `adj` of the comparison
`D(F)(G E ⊗ᴸ K) ⟶ D(F) G E ⊗ᴸ D(F) K` followed by the counit of `adj`. -/
noncomputable abbrev mapDerivedCategoryProjectionMap (E : DerivedCategory D) :
    (curriedTensor (DerivedCategory C)).obj (G.obj E) ⟶
      (F.mapDerivedCategory ⋙ (curriedTensor (DerivedCategory D)).obj E) ⋙ G :=
  (adj.rightAdjointProjectionMap F.mapDerivedCategoryTensorComparison).app E

lemma mapDerivedCategoryProjectionMap_app (E : DerivedCategory D) (K : DerivedCategory C) :
    (mapDerivedCategoryProjectionMap adj E).app K =
      adj.homEquiv _ _ ((F.mapDerivedCategoryTensorComparison.app (G.obj E)).app K ≫
        adj.counit.app E ▷ F.mapDerivedCategory.obj K) :=
  rfl

/-- The projection map `G E ⊗ᴸ 𝟙 ⟶ G (E ⊗ᴸ D(F) 𝟙)` is an isomorphism. -/
lemma isIso_mapDerivedCategoryProjectionMap_app_tensorUnit (E : DerivedCategory D) :
    IsIso ((mapDerivedCategoryProjectionMap adj E).app (𝟙_ _)) := by
  let _ := F.mapDerivedCategoryOplaxMonoidal
  have := F.isIso_mapDerivedCategoryOplaxMonoidal_η
  exact adj.isIso_rightAdjointProjectionMap_app_app_tensorUnit _ (fun _ _ ↦ rfl) E

/-- The projection map commutes with the shifts, for the commutation of `G` with the shifts
induced by the adjunction `D(F) ⊣ G`. -/
lemma commShift_mapDerivedCategoryProjectionMap (E : DerivedCategory D) :
    letI := adj.rightAdjointCommShift ℤ
    NatTrans.CommShift (mapDerivedCategoryProjectionMap adj E) ℤ := by
  let _ := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact Adjunction.commShift_rightAdjointProjectionMap_app adj _ E

/-- If `G` does not lower the cohomological degree, `E` is bounded below and the projection map
`τ_E : G E ⊗ᴸ K ⟶ G (E ⊗ᴸ D(F) K)` is an isomorphism at the flat objects placed in degree `0`,
then it is an isomorphism at every `K` of Tor amplitude in `[b, ∞)`.

Represent `K` by a K-flat complex `P` of flat objects vanishing below `b` with `F(P)` K-flat. In
a fixed degree `q`, for `N` large, both sides vanish in degrees `q` and `q + 1` on the stupid
truncation `σ^{≥ N + 1} P`, a K-flat complex concentrated in degrees `≥ N + 1`, so the map in
degree `q` is the one at `σ^{≤ N} P`, a bounded complex of flat objects. -/
theorem isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE
    (hG : ∀ (Y : DerivedCategory D) (n : ℤ), Y.IsGE n → (G.obj Y).IsGE n)
    (E : DerivedCategory D) (a : ℤ) [E.IsGE a]
    (hflat : ∀ M : C, ObjectProperty.flat M →
      IsIso ((mapDerivedCategoryProjectionMap adj E).app ((singleFunctor C 0).obj M)))
    (K : DerivedCategory C) (b : ℤ) (hK : torAmplitudeGE C b K) :
    IsIso ((mapDerivedCategoryProjectionMap adj E).app K) := by
  let _ := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have := commShift_mapDerivedCategoryProjectionMap adj E
  obtain ⟨P, _, hP, hPk, hFP, ⟨eP⟩⟩ := F.exists_kFlat_model_of_torAmplitudeGE hK
  refine (NatTrans.isIso_app_iff_of_iso (mapDerivedCategoryProjectionMap adj E) eP).1 ?_
  rw [DerivedCategory.isIso_iff]
  intro q
  have := hG E a inferInstance
  let N : ℤ := q - a + 1
  have ac := ComplexShape.Embedding.embeddingUpInt_areComplementary N (N + 1) rfl
  have hS : (P.shortComplexStupidTrunc ac).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun i ↦ (P.shortComplexStupidTruncSplitting ac i).shortExact
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  let σ := P.stupidTrunc (ComplexShape.embeddingUpIntGE (N + 1))
  have hσ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat σ :=
    CochainComplex.kFlat_stupidTruncGE P hP hPk N
  have hFσ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((F.mapHomologicalComplex _).obj σ) :=
    CochainComplex.kFlat_mapHomologicalComplex_obj_stupidTruncGE F P hP hFP N
  have : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj σ) (N + 1) :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
      F.map_isZero (CochainComplex.isZero_of_isStrictlyGE σ (N + 1) i hi)
  -- the source is concentrated in degrees `≥ a + N + 1` on `σ^{≥ N + 1} P`
  have h₁ : (G.obj E ⊗ Q.obj σ).IsGE (a + (N + 1)) :=
    isGE_tensor_of_torAmplitudeGE_right (torAmplitudeGE_Q_obj_of_kFlat σ (N + 1) hσ) _ a
  -- and so is the target
  have h₂ : (G.obj (E ⊗ F.mapDerivedCategory.obj (Q.obj σ))).IsGE (a + (N + 1)) := by
    have := isGE_tensor_of_torAmplitudeGE_right
      (torAmplitudeGE_Q_obj_of_kFlat _ (N + 1) hFσ) E a
    exact hG _ _ (TStructure.t.isGE_of_iso (X := E ⊗ Q.obj ((F.mapHomologicalComplex _).obj σ))
      (whiskerLeftIso E (F.mapDerivedCategoryFactors.app σ).symm) _)
  have : CochainComplex.IsStrictlyGE (P.shortComplexStupidTrunc ac).X₃ b :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (P.stupidTrunc (ComplexShape.embeddingUpIntLE N)) b)
  have : CochainComplex.IsStrictlyLE (P.shortComplexStupidTrunc ac).X₃ N :=
    inferInstanceAs (CochainComplex.IsStrictlyLE
      (P.stupidTrunc (ComplexShape.embeddingUpIntLE N)) N)
  have h₃ : IsIso ((mapDerivedCategoryProjectionMap adj E).app
      (DerivedCategory.triangleOfSES hS).obj₃) :=
    DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE_of_prop
      (mapDerivedCategoryProjectionMap adj E) ObjectProperty.flat hflat _ b N
      (HomologicalComplex.prop_stupidTrunc_X _ P _ hP)
  refine DerivedCategory.isIso_homologyFunctor_map_app_obj₂_of_obj₃
    (mapDerivedCategoryProjectionMap adj E) (DerivedCategory.triangleOfSES hS) hT q
    (DerivedCategory.isZero_of_isGE _ (a + (N + 1)) q (by lia) (hX := h₁))
    (DerivedCategory.isZero_of_isGE _ (a + (N + 1)) (q + 1) (by lia) (hX := h₁))
    (DerivedCategory.isZero_of_isGE _ (a + (N + 1)) q (by lia) (hX := h₂))
    (DerivedCategory.isZero_of_isGE _ (a + (N + 1)) (q + 1) (by lia) (hX := h₂)) inferInstance

end CategoryTheory.Functor
