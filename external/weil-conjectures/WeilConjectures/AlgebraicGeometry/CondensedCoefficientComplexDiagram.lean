/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjColimit

/-! # Canonical coefficient diagrams on complexes -/

@[expose] public section
universe v u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod
section
variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  [HasCoequalizers A] [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
  [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
  {R S T B : A} [MonObj R] [IsCommMonObj R] [MonObj S] [MonObj T] [MonObj B]
  (f : R ⟶ S) [IsMonHom f] (g : R ⟶ T) [IsMonHom g]
  (e : B ⟶ S) [IsMonHom e] (e' : B ⟶ T) [IsMonHom e']
  (a : S ⟶ T) [IsMonHom a] (hf : f ≫ a = g) (he : e ≫ a = e')

/-- Extension by a coefficient inclusion, with both objects restricted to a common ring.
The map is constructed from the scalar-extension adjunction, not chosen by existence.
(auxiliary; not a blueprint node) -/
noncomputable def mixedScalarMap (M : Mod A R) :
    (comap e).obj ((extendScalars f).obj M) ⟶
      (comap e').obj ((extendScalars g).obj M) :=
  let t : M ⟶ (comap f).obj ((comap a).obj ((extendScalars g).obj M)) :=
    Hom.mk' (extendUnit g M).hom (by
      have h := act_hom (extendUnit g M)
      change γ[R,M.X] ≫ (extendUnit g M).hom =
        R ◁ (extendUnit g M).hom ≫ f ▷ _ ≫ a ▷ _ ≫ γ[T,(extendScalarsObj g M).X]
      change γ[R,M.X] ≫ (extendUnit g M).hom =
        R ◁ (extendUnit g M).hom ≫ g ▷ _ ≫ γ[T,(extendScalarsObj g M).X] at h
      rw [h]
      rw [← comp_whiskerRight_assoc, hf])
  let b := extendHom f t
  Hom.mk' b.hom (by
    change (e ▷ _ ≫ γ[S,(extendScalarsObj f M).X]) ≫ b.hom =
      B ◁ b.hom ≫ e' ▷ _ ≫ γ[T,(extendScalarsObj g M).X]
    rw [Category.assoc, act_hom b]
    change e ▷ _ ≫ S ◁ b.hom ≫ a ▷ _ ≫
      γ[T,(extendScalarsObj g M).X] = _
    rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, he,
      whisker_exchange_assoc])

@[reassoc]
lemma extendπ_mixedScalarMap (M : Mod A R) :
    extendπ f M ≫ (mixedScalarMap f g e e' a hf he M).hom = a ▷ M.X ≫ extendπ g M := by
  dsimp only [mixedScalarMap, Hom.mk']
  rw [extendπ_extendHom]
  change S ◁ (extendUnit g M).hom ≫ a ▷ _ ≫ γ[T,(extendScalarsObj g M).X] = _
  rw [whisker_exchange_assoc, extendUnit_hom, whiskerLeft_extendUnitHom_smul']

lemma mixedScalarMap_naturality {M N : Mod A R} (m : M ⟶ N) :
    mixedScalarMap f g e e' a hf he M ≫ (comap e').map ((extendScalars g).map m) =
      (comap e).map ((extendScalars f).map m) ≫ mixedScalarMap f g e e' a hf he N := by
  apply hom_ext
  apply (cancel_epi (extendπ f M)).mp
  simp only [comp_hom', comap_map_hom, extendScalars_map,
    extendπ_mixedScalarMap_assoc, extendπ_extendScalarsMap_assoc,
    extendπ_mixedScalarMap, extendπ_extendScalarsMap]
  rw [whisker_exchange_assoc]

/-- The natural coefficient-inclusion transformation on restricted extensions. -/
noncomputable def mixedScalarNatTrans :
    extendScalars f ⋙ comap e ⟶ extendScalars g ⋙ comap e' where
  app := mixedScalarMap f g e e' a hf he
  naturality _ _ m := (mixedScalarMap_naturality f g e e' a hf he m).symm

end

section
variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  [HasCoequalizers A] [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
  [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
  {R S B : A} [MonObj R] [IsCommMonObj R] [MonObj S] [MonObj B]
  (f : R ⟶ S) [IsMonHom f] (e : B ⟶ S) [IsMonHom e]

lemma mixedScalarMap_id (M : Mod A R) :
    mixedScalarMap f f e e (𝟙 S) (by simp) (by simp) M = 𝟙 _ := by
  apply hom_ext
  apply (cancel_epi (extendπ f M)).mp
  rw [extendπ_mixedScalarMap, id_whiskerRight, Category.id_comp, id_hom']
  exact (Category.comp_id (extendπ f M)).symm

end

section
variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  [HasCoequalizers A] [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
  [∀ Y : A, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
  {R S T U B : A} [MonObj R] [IsCommMonObj R]
  [MonObj S] [MonObj T] [MonObj U] [MonObj B]
  (f : R ⟶ S) [IsMonHom f] (g : R ⟶ T) [IsMonHom g] (h : R ⟶ U) [IsMonHom h]
  (e : B ⟶ S) [IsMonHom e] (e' : B ⟶ T) [IsMonHom e'] (e'' : B ⟶ U) [IsMonHom e'']
  (a : S ⟶ T) [IsMonHom a] (b : T ⟶ U) [IsMonHom b]
  (hf : f ≫ a = g) (hg : g ≫ b = h) (he : e ≫ a = e') (he' : e' ≫ b = e'')

lemma mixedScalarMap_comp (M : Mod A R) :
    mixedScalarMap f h e e'' (a ≫ b) (by rw [← Category.assoc, hf, hg])
        (by rw [← Category.assoc, he, he']) M =
      mixedScalarMap f g e e' a hf he M ≫ mixedScalarMap g h e' e'' b hg he' M := by
  apply hom_ext
  apply (cancel_epi (extendπ f M)).mp
  simp only [comp_hom', extendπ_mixedScalarMap_assoc,
    extendπ_mixedScalarMap, comp_whiskerRight_assoc]

end
end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The termwise coefficient functor, with scalars restricted to `E`. -/
noncomputable def coefficientComplexStage {E F G : FiniteIntermediateField ℓ}
    (he : E ≤ G) (hf : F ≤ G) :=
  (Mod.extendScalars (padicSubfieldRingObjMap X ℓ hf)).mapHomologicalComplex (.up ℤ) ⋙
    (Mod.comap (padicSubfieldRingObjMap X ℓ he)).mapHomologicalComplex (.up ℤ)

/-- A coefficient inclusion acts on complexes by the natural scalar-inclusion map. -/
noncomputable def coefficientComplexMap {E F G G' : FiniteIntermediateField ℓ}
    (he : E ≤ G) (hf : F ≤ G) (he' : E ≤ G') (hf' : F ≤ G') (h : G ≤ G')
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    (coefficientComplexStage X ℓ he hf).obj C ⟶
      (coefficientComplexStage X ℓ he' hf').obj C :=
  (NatTrans.mapHomologicalComplex
    (Mod.mixedScalarNatTrans (padicSubfieldRingObjMap X ℓ hf)
      (padicSubfieldRingObjMap X ℓ hf') (padicSubfieldRingObjMap X ℓ he)
      (padicSubfieldRingObjMap X ℓ he') (padicSubfieldRingObjMap X ℓ h)
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ hf h)
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ he h)) (.up ℤ)).app C

/-- The canonical coefficient diagram, with actual termwise scalar inclusions as maps.
Source: the coefficient-algebra construction of the archived `TwoColimit.lean`.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexDiagram {E F : FiniteIntermediateField ℓ}
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    {I : Type (u + 1)} [SmallCategory I] (H : I ⥤ FiniteIntermediateField ℓ)
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    I ⥤ CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ where
  obj i := (coefficientComplexStage X ℓ (he i) (hf i)).obj C
  map {i j} f := coefficientComplexMap X ℓ (he i) (hf i) (he j) (hf j)
    (leOfHom (H.map f)) C
  map_id i := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [coefficientComplexMap, NatTrans.mapHomologicalComplex_app_f,
      Mod.mixedScalarNatTrans, HomologicalComplex.id_f]
    have h : padicSubfieldRingObjMap X ℓ (leOfHom (H.map (𝟙 i))) = 𝟙 _ := by
      change (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjMap ℓ _) = _
      rw [Profinite.padicSubfieldRingObjMap_id, CategoryTheory.Functor.map_id]
    simp only [h, Mod.mixedScalarMap_id]
    rfl
  map_comp {i j k} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [coefficientComplexMap, NatTrans.mapHomologicalComplex_app_f,
      Mod.mixedScalarNatTrans, HomologicalComplex.comp_f]
    have h : padicSubfieldRingObjMap X ℓ (leOfHom (H.map (f ≫ g))) =
        padicSubfieldRingObjMap X ℓ (leOfHom (H.map f)) ≫
          padicSubfieldRingObjMap X ℓ (leOfHom (H.map g)) :=
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _).symm
    simp only [h]
    exact Mod.mixedScalarMap_comp
      (padicSubfieldRingObjMap X ℓ (hf i)) (padicSubfieldRingObjMap X ℓ (hf j))
      (padicSubfieldRingObjMap X ℓ (hf k)) (padicSubfieldRingObjMap X ℓ (he i))
      (padicSubfieldRingObjMap X ℓ (he j)) (padicSubfieldRingObjMap X ℓ (he k))
      (padicSubfieldRingObjMap X ℓ (leOfHom (H.map f)))
      (padicSubfieldRingObjMap X ℓ (leOfHom (H.map g)))
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _)
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _)
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _)
      (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _)
      (C.X n)

/-- Extension to the algebraic closure followed by restriction to `E`, degreewise. -/
noncomputable def coefficientComplexVertex {E F : FiniteIntermediateField ℓ}
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :=
  ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex (.up ℤ)).obj
    (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex
      (.up ℤ)).obj C)

/-- The coefficient inclusion into the algebraic closure on complexes. -/
noncomputable def coefficientComplexToAlgCl {E F G : FiniteIntermediateField ℓ}
    (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    (coefficientComplexStage X ℓ he hf).obj C ⟶ coefficientComplexVertex X ℓ (E := E) C :=
  (NatTrans.mapHomologicalComplex
    (Mod.mixedScalarNatTrans (padicSubfieldRingObjMap X ℓ hf)
      (padicSubfieldRingObjToPadicAlgCl X ℓ F) (padicSubfieldRingObjMap X ℓ he)
      (padicSubfieldRingObjToPadicAlgCl X ℓ E) (padicSubfieldRingObjToPadicAlgCl X ℓ G)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hf)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ he)) (.up ℤ)).app C

/-- The canonical coefficient cocone, with the actual algebraic-closure complex as vertex.
Source: archived `TwoColimit.lean`, coefficient-algebra construction.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexCocone {E F : FiniteIntermediateField ℓ}
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    {I : Type (u + 1)} [SmallCategory I] (H : I ⥤ FiniteIntermediateField ℓ)
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    Cocone (coefficientComplexDiagram X ℓ C H he hf) where
  pt := coefficientComplexVertex X ℓ C
  «ι» :=
    { app i := coefficientComplexToAlgCl X ℓ (he i) (hf i) C
      naturality i j f := by
        change coefficientComplexMap X ℓ (he i) (hf i) (he j) (hf j)
          (leOfHom (H.map f)) C ≫ coefficientComplexToAlgCl X ℓ (he j) (hf j) C =
            coefficientComplexToAlgCl X ℓ (he i) (hf i) C ≫ 𝟙 _
        rw [Category.comp_id]
        apply HomologicalComplex.hom_ext
        intro n
        simp only [HomologicalComplex.comp_f, coefficientComplexMap,
          coefficientComplexToAlgCl, NatTrans.mapHomologicalComplex_app_f,
          Mod.mixedScalarNatTrans]
        apply Mod.hom_ext
        apply (cancel_epi (Mod.extendπ (padicSubfieldRingObjMap X ℓ (hf i)) (C.X n))).mp
        simp only [Mod.comp_hom', Mod.extendπ_mixedScalarMap_assoc,
          Mod.extendπ_mixedScalarMap]
        rw [← comp_whiskerRight_assoc, padicSubfieldRingObjMap_comp_toPadicAlgCl] }

/-- Ordinary coefficient tensor transitivity, before localization.
Source: uniqueness of the scalar-extension adjoints.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientTensorIso {E G : FiniteIntermediateField ℓ} (h : E ≤ G) :=
  (Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldRingObjToPadicAlgCl X ℓ G)).symm ≪≫
    Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)

/-- Tensor transitivity applied degree by degree to coefficient complexes.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexTensorIso {E G : FiniteIntermediateField ℓ} (h : E ≤ G) :=
  CategoryTheory.Functor.mapHomologicalComplexCompIso (coefficientTensorIso X ℓ h) (.up ℤ)

/-- The ordinary adjunction mate of tensor transitivity on a coefficient complex.
The next theorem identifies this actual morphism with the coefficient inclusion.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexTransposedMap {E F G : FiniteIntermediateField ℓ}
    (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    (coefficientComplexStage X ℓ he hf).obj C ⟶ coefficientComplexVertex X ℓ C :=
  let adj := Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let adjE := Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ he)
  let extG := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ G)
  (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _
    ((coefficientComplexTensorIso X ℓ he).inv.app
        ((coefficientComplexStage X ℓ he hf).obj C) ≫
      (extG.mapHomologicalComplex (.up ℤ)).map
        ((adjE.mapHomologicalComplex (.up ℤ)).counit.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hf)).mapHomologicalComplex
            (.up ℤ)).obj C)) ≫
      (coefficientComplexTensorIso X ℓ hf).hom.app C)

/-- The exact scalar-extension comparison on a coefficient complex.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexExtensionIso {F G : FiniteIntermediateField ℓ}
    (h : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    (derivedExtendScalarsSubfield X ℓ h).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
          (.up ℤ)).obj C) :=
  let F := Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)
  (CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory.{u + 1, u + 1,
    u + 1, u + 1, u + 2, u + 2} F).app (DerivedCategory.Q.obj C) ≪≫
    F.mapDerivedCategoryFactors.app C

/-- The exact extension-to-algebraic-closure comparison on a coefficient complex.
(auxiliary; not a blueprint node) -/
noncomputable def coefficientComplexAlgClExtensionIso (F : FiniteIntermediateField ℓ)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ F).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex
          (.up ℤ)).obj C) :=
  let G := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)
  (CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory.{u + 1, u + 1,
    u + 1, u + 1, u + 2, u + 2} G).app (DerivedCategory.Q.obj C) ≪≫
    G.mapDerivedCategoryFactors.app C

/-- Localization of the termwise stage is the prescribed composite derived functor. -/
noncomputable def coefficientComplexStageIso {E F G : FiniteIntermediateField ℓ}
    (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C) ≅
      (finiteCoefficientDerivedRestriction X ℓ he).obj
        ((derivedExtendScalarsSubfield X ℓ hf).obj (DerivedCategory.Q.obj C)) :=
  ((Mod.comap (padicSubfieldRingObjMap X ℓ he)).mapDerivedCategoryFactors.app
      (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hf)).mapHomologicalComplex
        (.up ℤ)).obj C)).symm ≪≫
    (finiteCoefficientDerivedRestriction X ℓ he).mapIso
      (coefficientComplexExtensionIso X ℓ hf C).symm

/-- Localization of the actual vertex is restriction of the prescribed derived extension. -/
noncomputable def coefficientComplexVertexIso {E F : FiniteIntermediateField ℓ}
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    DerivedCategory.Q.obj (coefficientComplexVertex X ℓ (E := E) C) ≅
      (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
        ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj (DerivedCategory.Q.obj C)) :=
  ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.app
      (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex
        (.up ℤ)).obj C)).symm ≪≫
    (finiteCoefficientDerivedFromAlgCl X ℓ E).mapIso
      (coefficientComplexAlgClExtensionIso X ℓ F C).symm

end AlgebraicGeometry.ProEtale
