/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedOrdinaryScalars
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedAcyclic
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedFlat

/-! # Scalar compatibility of the normalized diagonal source

Source: diagonal tower coefficient changes, paragraph (1), and the supported-source
normalization in the diagonal tower trace construction.
(blueprint: lem-diagonal-supported-scalar-source).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] canonicalDiagonalRightDerived
  RestrictionSquare.mate Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction

section SingleSquares

universe a v w
variable {A B C D : Type a} [Category.{v} A] [Category.{v} B]
  [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
  [F.Additive] [G.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] in
private theorem cochain_single_square (q : F ⋙ V ≅ U ⋙ G) (M : A) :
    (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (U.obj M) =
    (V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (F.obj M) ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (q.hom.app M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
    simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using!
      congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((U ⋙ G).obj M)).inv)
        (q.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).symm
  · exact ((F ⋙ V).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).eq_of_src _ _

private theorem augmentation_eq (R : DiagonalRightDerived F) (M : A) :
    diagonalTraceRightSingle F R M =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        R.η.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) := by
  simp only [diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [R.R.map_id, Category.comp_id]

private theorem single_factors (M : A) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app M =
      U.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) := by
  erw [← U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M]
  erw [Iso.hom_inv_id_app_assoc]

private theorem restriction_single_square
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (q : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG q) (M : A) :
    V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) ≫
        s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (q.hom.app M) ≫
        diagonalTraceRightSingle G RG (U.obj M) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cU := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  let cV := HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0
  have hc : (V.mapHomologicalComplex (.up ℤ)).map (cF.inv.app M) ≫
      (NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K ≫
      (G.mapHomologicalComplex (.up ℤ)).map (cU.hom.app M) =
      cV.hom.app (F.obj M) ≫ (HomologicalComplex.single D (.up ℤ) 0).map
        (q.hom.app M) ≫ cG.inv.app (U.obj M) := by
    apply (cancel_epi ((V.mapHomologicalComplex (.up ℤ)).map (cF.hom.app M))).mp
    apply (cancel_mono (cG.hom.app (U.obj M))).mp
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact cochain_single_square F G U V q M
  rw [augmentation_eq, augmentation_eq, single_factors U, single_factors V]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (s.normalization K)]
  change V.mapDerivedCategory.map (DerivedCategory.Q.map (cF.inv.app M)) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K) ≫
      RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
      RG.R.map (DerivedCategory.Q.map (cU.hom.app M)) =
    V.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map (cV.hom.app (F.obj M)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (q.hom.app M)) ≫
      DerivedCategory.Q.map (cG.inv.app (U.obj M)) ≫
      RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))
  have hn := RG.η.naturality (cU.hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [← hn]
  erw [V.mapDerivedCategoryFactors.hom.naturality_assoc (cF.inv.app M)]
  congr 1
  simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp_assoc]
  exact congrArg (fun z ↦ DerivedCategory.Q.map z ≫
    RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))) hc

private theorem restriction_single_square_inv
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (q : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG q) (M : A) :
    diagonalTraceRightSingle G RG (U.obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
        s.iso.inv.app ((DerivedCategory.singleFunctor A 0).obj M) =
      (DerivedCategory.singleFunctor D 0).map (q.inv.app M) ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
        V.mapDerivedCategory.map (diagonalTraceRightSingle F RF M) := by
  apply (cancel_mono (s.iso.hom.app _ ≫
    RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [RG.R.map_id, Category.comp_id]
  rw [restriction_single_square F G U V RF RG q s M]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem augmentation_naturality (R : DiagonalRightDerived F)
    {M N : A} (v : M ⟶ N) :
    (DerivedCategory.singleFunctor B 0).map (F.map v) ≫
        diagonalTraceRightSingle F R N =
      diagonalTraceRightSingle F R M ≫ R.R.map
        ((DerivedCategory.singleFunctor A 0).map v) := by
  rw [augmentation_eq, augmentation_eq]
  erw [← DerivedCategory.Q.map_comp_assoc]
  erw [(HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality v]
  erw [DerivedCategory.Q.map_comp, Category.assoc]
  have hn := R.η.naturality
    ((HomologicalComplex.single A (.up ℤ) 0).map v)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [hn]
  rw [Category.assoc]
  rfl

end SingleSquares

private theorem three_module_iso_app
    {B C : Type*} [Category B] [Category C] [MonoidalCategory C]
    {A : C} [MonObj A] {F₀ F₁ F₂ F₃ : B ⥤ Mod C A}
    (i : F₀ ≅ F₁) (j : F₁ ≅ F₂) (k : F₂ ≅ F₃) (M : B)
    {a : (F₀.obj M).X ⟶ (F₁.obj M).X}
    {b : (F₁.obj M).X ⟶ (F₂.obj M).X}
    {c : (F₂.obj M).X ⟶ (F₃.obj M).X}
    (ha : (i.hom.app M).hom = a) (hb : (j.hom.app M).hom = b)
    (hc : (k.hom.app M).hom = c) :
    ((i.app M ≪≫ j.app M ≪≫ k.app M).symm.inv).hom = a ≫ b ≫ c := by
  simp only [Iso.symm_inv, Iso.trans_hom, Iso.app_hom, Mod.comp_hom', ha, hb, hc]

private theorem three_iso_hom_app
    {C D : Type*} [Category C] [Category D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (i : F₀ ≅ F₁) (j : F₁ ≅ F₂) (k : F₂ ≅ F₃) (M : C) :
    (i ≪≫ j ≪≫ k).hom.app M = i.hom.app M ≫ j.hom.app M ≫ k.hom.app M := rfl

private def normalized_three_module_iso
    {B C : Type*} [Category B] [Category C] [MonoidalCategory C]
    {A : C} [MonObj A] {F₀ F₁ F₂ F₃ : B ⥤ Mod C A}
    (i : F₀ ≅ F₁) (j : F₁ ≅ F₂) (k : F₂ ≅ F₃) (M : B)
    (q : (F₀.obj M).X ≅ (F₃.obj M).X)
    {a : (F₀.obj M).X ⟶ (F₁.obj M).X}
    {b : (F₁.obj M).X ⟶ (F₂.obj M).X}
    {c : (F₂.obj M).X ⟶ (F₃.obj M).X}
    (ha : (i.hom.app M).hom = a) (hb : (j.hom.app M).hom = b)
    (hc : (k.hom.app M).hom = c) (hq : q.hom = a ≫ b ≫ c) :
    {e : F₃.obj M ≅ F₀.obj M // e.inv.hom = q.hom} := by
  have he : ((i.app M ≪≫ j.app M ≪≫ k.app M).hom).hom = q.hom :=
    (three_module_iso_app i j k M ha hb hc).trans hq.symm
  refine ⟨(Mod.isoMk q ?_).symm, rfl⟩
  rw [← he]
  exact Mod.act_hom _

section OrdinarySource

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {P W : Scheme.{u}} (k : P ⟶ W) (f : W ⟶ P) (h : k ≫ f = 𝟙 P)
  (M : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P))

private def ordinaryCompositionAux
    (g : P ⟶ P) (hg : g = 𝟙 P)
    (i : CondensedRing.lowerStar Λ k ⋙ CondensedRing.lowerStar Λ f ≅
      CondensedRing.lowerStar Λ g)
    (j : ProEtale.lowerStar Ab.{u + 1} k ⋙ ProEtale.lowerStar Ab.{u + 1} f ≅
      ProEtale.lowerStar Ab.{u + 1} g)
    (hj : (i.hom.app M).hom = j.hom.app M.X) :
    {e : M ≅ (CondensedRing.lowerStar Λ f).obj ((CondensedRing.lowerStar Λ k).obj M) //
      HEq e.inv.hom ((j ≪≫ ProEtale.lowerStarCongr Ab.{u + 1} hg ≪≫
        ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X)} := by
  subst g
  let q₀ := j ≪≫ ProEtale.lowerStarCongr Ab.{u + 1} (rfl : 𝟙 P = 𝟙 P) ≪≫
    ProEtale.lowerStarId Ab.{u + 1} P
  let q : ((CondensedRing.lowerStar Λ f).obj
      ((CondensedRing.lowerStar Λ k).obj M)).X ≅ M.X :=
    { hom := q₀.hom.app M.X
      inv := q₀.inv.app M.X
      hom_inv_id := q₀.hom_inv_id_app M.X
      inv_hom_id := q₀.inv_hom_id_app M.X }
  let n := normalized_three_module_iso i
    (CondensedRing.lowerStarCongr Λ (rfl : 𝟙 P = 𝟙 P))
    (CondensedRing.lowerStarId Λ P) M q hj
    (CondensedRing.lowerStarCongr_hom_app_hom Λ (rfl : 𝟙 P = 𝟙 P) M)
    (CondensedRing.lowerStarId_hom_app_hom Λ P M)
    (three_iso_hom_app j (ProEtale.lowerStarCongr Ab.{u + 1} (rfl : 𝟙 P = 𝟙 P))
      (ProEtale.lowerStarId Ab.{u + 1} P) M.X)
  exact ⟨n.val, heq_of_eq n.property⟩

private def ordinaryCompositionData :
    {e : M ≅ (CondensedRing.lowerStar Λ f).obj ((CondensedRing.lowerStar Λ k).obj M) //
      HEq e.inv.hom
        ((ProEtale.lowerStarComp Ab.{u + 1} k f ≪≫
          ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
          ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X)} :=
  ordinaryCompositionAux Λ k f M (k ≫ f) h (CondensedRing.lowerStarComp Λ k f)
    (ProEtale.lowerStarComp Ab.{u + 1} k f)
    (CondensedRing.lowerStarComp_hom_app_hom Λ k f M)

private theorem ordinaryComposition_nonempty :
    Nonempty {e : M ≅ (CondensedRing.lowerStar Λ f).obj
        ((CondensedRing.lowerStar Λ k).obj M) //
      HEq e.inv.hom
        ((ProEtale.lowerStarComp Ab.{u + 1} k f ≪≫
          ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
          ProEtale.lowerStarId Ab.{u + 1} P).hom.app M.X)} :=
  ⟨ordinaryCompositionData Λ k f h M⟩

end OrdinarySource

private theorem regular_app_heq
    {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    {F G : C ⥤ D} (v : F ⟶ G) (A : C) [MonObj A] :
    HEq (v.app (Mod.regular A).X) (v.app A) := HEq.rfl

private theorem normalizedSource_nonempty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)] (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    Nonempty (DiagonalTrace.NormalizedSource (CondensedRing.lowerStar Λ f)
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f))
      (source Λ Y) (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (diagonalImmersion Y ≫ f = 𝟙 _) (SupportNormalization Λ Y f)) := by
  obtain ⟨⟨i, hi⟩⟩ := ordinaryComposition_nonempty Λ (diagonalImmersion Y) f h
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  exact ⟨{ over_eq := h
           iso := i
           normalization := hi.trans (regular_app_heq
             ((ProEtale.lowerStarComp Ab.{u + 1} (diagonalImmersion Y) f ≪≫
               ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
               ProEtale.lowerStarId Ab.{u + 1} (ProjectiveLine Y)).hom)
             (condensedRingObj Λ (ProjectiveLine Y)))
           acyclic := diagonal_supported_acyclic Λ Y f h }⟩

section InverseCarrier

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]
  {R S : C} [MonObj R] [MonObj S] {R' S' : D} [MonObj R'] [MonObj S']
  (a : R ⟶ S) [IsMonHom a] (b : R' ⟶ S') [IsMonHom b]
  (c : R' ⟶ F.obj R) [IsMonHom c] (d : S' ⟶ F.obj S) [IsMonHom d]
  (h : b ≫ d = c ≫ F.map a)

private theorem comap_square_inv_hom (M : Mod C S) :
    ((Mod.comapMapModComapIso F a b c d h).inv.app M).hom = 𝟙 (F.obj M.X) := by
  have hh := Mod.comapMapModComapIso_hom_app_hom F a b c d h M
  have hi := congrArg Mod.Hom.hom
    ((Mod.comapMapModComapIso F a b c d h).inv_hom_id_app M)
  simp only [Mod.comp_hom', Mod.id_hom', hh] at hi
  change ((Mod.comapMapModComapIso F a b c d h).inv.app M).hom ≫
    𝟙 (F.obj M.X) = 𝟙 (F.obj M.X) at hi
  erw [Category.comp_id] at hi
  exact hi

end InverseCarrier

private theorem comapLowerStarIso_inv_hom
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ' X) :
    ((CondensedRing.comapLowerStarIso a f).inv.app M).hom =
      𝟙 ((ProEtale.lowerStar Ab.{u + 1} f).obj M.X) :=
  comap_square_inv_hom (ProEtale.lowerStar Ab.{u + 1} f)
    (coefficientMap a X) (coefficientMap a S)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ' f)
    (condensedPushforwardHom_comp_map_coefficientMap a f).symm M

private theorem iso_square_of_inv_square
    {C D : Type*} [Category C] [Category D] (V : D ⥤ C)
    {N P : C} {N' P' : D} (i : N ≅ P) (j : N' ≅ P')
    (x : P ⟶ V.obj P') (v : N ⟶ V.obj N')
    (h : x ≫ V.map j.inv = i.inv ≫ v) : i.hom ≫ x = v ≫ V.map j.hom := by
  apply (cancel_mono (V.map j.inv)).mp
  simp only [Category.assoc, ← V.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

private theorem ordinary_source_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (i : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ≅
      (CondensedRing.lowerStar Λ f).obj (source Λ Y))
    (j : Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)) ≅
      (CondensedRing.lowerStar Λ' f).obj (source Λ' Y))
    (hi : SupportNormalization Λ Y f i h) (hj : SupportNormalization Λ' Y f j h)
    (v : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ⟶
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).obj
        (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y))))
    (hv : v.hom = coefficientMap a (ProjectiveLine Y)) :
    i.hom ≫ (CondensedRing.lowerStar Λ f).map (supportMap a Y v) ≫
        (CondensedRing.comapLowerStarIso a f).inv.app (source Λ' Y) =
      v ≫ (Mod.comap (coefficientMap a (ProjectiveLine Y))).map j.hom := by
  apply iso_square_of_inv_square
    (Mod.comap (coefficientMap a (ProjectiveLine Y))) i j
      ((CondensedRing.lowerStar Λ f).map (supportMap a Y v) ≫
        (CondensedRing.comapLowerStarIso a f).inv.app (source Λ' Y)) v
  apply Mod.hom_ext
  have hi' := eq_of_heq hi
  have hj' := eq_of_heq hj
  let q := ProEtale.lowerStarComp Ab.{u + 1} (diagonalImmersion Y) f ≪≫
    ProEtale.lowerStarCongr Ab.{u + 1} h ≪≫
    ProEtale.lowerStarId Ab.{u + 1} (ProjectiveLine Y)
  have hn := q.hom.naturality (coefficientMap a (ProjectiveLine Y))
  simp only [Mod.comp_hom', Mod.comap_map_hom, CondensedRing.lowerStar_map_hom, supportMap,
    comapLowerStarIso_inv_hom, Functor.map_comp, hi', hj', hv]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  simpa only [Functor.comp_map, Functor.id_map] using hn

private theorem map_square_of_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} {P Q : D} (a : P ⟶ F.obj M) (b : F.obj N ⟶ Q)
    {u v : M ⟶ N} (hu : u = v) {w : P ⟶ Q}
    (h : a ≫ F.map v ≫ b = w) : a ≫ F.map u ≫ b = w := by
  subst v
  exact h

section Mates

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {E : A ⥤ B} {U : B ⥤ A} {E' : C ⥤ D} {U' : D ⥤ C}
  (adj : E ⊣ U) (adj' : E' ⊣ U') {F : A ⥤ C} {G : B ⥤ D}
  (q : G ⋙ U' ≅ U ⋙ F)

private theorem mate_transpose {M : A} {N : B} (v : E.obj M ⟶ N) :
    adj'.homEquiv _ _
      ((Adjunction.pushHomOfComapIso adj adj' q).app M ≫ G.map v) =
    F.map (adj.homEquiv _ _ v) ≫ q.inv.app N := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  have hm := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ q.inv) M
  change F.map (adj.unit.app M) ≫ q.inv.app (E.obj M) =
    adj'.unit.app (F.obj M) ≫ U'.map
      ((Adjunction.pushHomOfComapIso adj adj' q).app M) at hm
  rw [← hm, Category.assoc]
  have hn := q.inv.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rw [← F.map_comp_assoc, adj.homEquiv_unit]

end Mates

section SourceAssembly

universe a v w
variable {A B A' B' : Type a} [Category.{v} A] [Category.{v} B]
  [Category.{v} A'] [Category.{v} B'] [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
  (F : A ⥤ B) (F' : A' ⥤ B') (U : A' ⥤ A) (V : B' ⥤ B)
  [F.Additive] [F'.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (R : DiagonalRightDerived F) (R' : DiagonalRightDerived F')
  (q : F' ⋙ V ≅ U ⋙ F)
  (s : DiagonalTrace.ExactSquareOfUniverses F' F U V R' R q)
  (E : DerivedCategory A ⥤ DerivedCategory A')
  (E' : DerivedCategory B ⥤ DerivedCategory B')
  (adj : E ⊣ U.mapDerivedCategory) (adj' : E' ⊣ V.mapDerivedCategory)

private theorem source_mate_square
    {M : A} {M' : A'} {N : B} {N' : B'}
    (u : M ⟶ U.obj M') (v : N ⟶ V.obj N')
    (e : E.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      (DerivedCategory.singleFunctor A' 0).obj M')
    (c : E'.obj ((DerivedCategory.singleFunctor B 0).obj N) ≅
      (DerivedCategory.singleFunctor B' 0).obj N')
    (he : adj.homEquiv _ _ e.hom =
      (DerivedCategory.singleFunctor A 0).map u ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app M')
    (hc : adj'.homEquiv _ _ c.hom =
      (DerivedCategory.singleFunctor B 0).map v ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app N')
    {P P' : Prop} {p : (N ≅ F.obj M) → P → Prop}
    {p' : (N' ≅ F'.obj M') → P' → Prop}
    (r : DiagonalTrace.NormalizedSource F R M N P p)
    (t : DiagonalTrace.NormalizedSource F' R' M' N' P' p')
    (h : r.iso.hom ≫ F.map u ≫ q.inv.app M' = v ≫ V.map t.iso.hom) :
    E'.map r.hom ≫ (Adjunction.pushHomOfComapIso adj adj' s.iso).app _ ≫
        R'.R.map e.hom = c.hom ≫ t.hom := by
  apply (adj'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, mate_transpose, he,
    Adjunction.homEquiv_naturality_right, hc]
  dsimp only [DiagonalTrace.NormalizedSource.hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (augmentation_naturality F R u)]
  rw [restriction_single_square_inv F' F U V R' R q s M']
  simp only [← Functor.map_comp_assoc]
  rw [h, Functor.map_comp, Category.assoc]
  erw [(V.mapDerivedCategorySingleFunctor 0).inv.naturality_assoc t.iso.hom]
  rfl

private theorem endpoint_normalization_comp
    {M : A} {P N : A'} (i : E.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      (DerivedCategory.singleFunctor A' 0).obj P) (j : P ≅ N)
    (v : M ⟶ U.obj P)
    (hi : adj.homEquiv _ _ i.hom = (DerivedCategory.singleFunctor A 0).map v ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app P) :
    adj.homEquiv _ _ (i ≪≫ (DerivedCategory.singleFunctor A' 0).mapIso j).hom =
      (DerivedCategory.singleFunctor A 0).map (v ≫ U.map j.hom) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app N := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Adjunction.homEquiv_naturality_right, hi,
    Category.assoc]
  have hn := (U.mapDerivedCategorySingleFunctor 0).inv.naturality j.hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← Functor.map_comp_assoc]

end SourceAssembly

private theorem endpoint_of_flat_ordinary_unit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    (M : Modules Λ X) (N : Modules Λ' X)
    (v : M ⟶ (Mod.comap (coefficientMap a X)).obj N)
    (hM : ObjectProperty.flat M)
    (hv : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv _ _).symm v)) :
    Nonempty (Endpoint a M N v.hom) := by
  let E : Modules Λ X ⥤ Modules Λ' X := Mod.extendScalars (coefficientMap a X)
  let U : Modules Λ' X ⥤ Modules Λ X := Mod.comap (coefficientMap a X)
  let adj : E ⊣ U := Mod.extendRestrictAdjunction (coefficientMap a X)
  let q : E.obj M ⟶ N := (adj.homEquiv _ _).symm v
  let : IsIso q := hv
  let j : E.obj M ≅ N := asIso q
  obtain ⟨i, hi, _⟩ := diagonal_flat_scalar_endpoint_iso a X M hM
  refine ⟨⟨⟨v, rfl⟩, i ≪≫ (DerivedCategory.singleFunctor (Modules Λ' X) 0).mapIso j, ?_⟩⟩
  have hj : Mod.extendUnit (coefficientMap a X) M ≫ U.map j.hom = v := by
    exact (adj.homEquiv _ _).apply_symm_apply v
  exact (endpoint_normalization_comp U (derivedScalars a X)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)) i j
      (Mod.extendUnit (coefficientMap a X) M) hi).trans
    (congrArg (fun z ↦ (DerivedCategory.singleFunctor (Modules Λ X) 0).map z ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app N) hj)

attribute [local irreducible] SupportNormalization DiagonalTrace.NormalizedSource.hom
  CondensedRing.comapLowerStarIso

/-- Closed diagonal support commutes with scalar extension, with the ordinary
composition normalization retained in the derived source map.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and
sk-prop-diagonal-tower-trace.proof.md, supported-source identification;
Stacks Tags 09AD, 09AA and 09AH.
(blueprint: lem-diagonal-supported-scalar-source).

Proof: On the diagonal the supported regular module is the regular module, and on
its open complement it is zero. Closed/open restriction is jointly conservative and
commutes with tensor, so this module is flat. The ordinary closed projection formula
identifies its scalar extension with the supported regular module for the new ring.
The extension unit followed by this comparison is precisely supportMap: closed
restriction gives the coefficient unit and open restriction gives the zero map.
Compute on the flat single complex. The scalar adjunction transpose is therefore an
isomorphism and gives e with its required normalization.

For the target normalized source, compose ordinary closed direct image with f_*,
use Delta f = id from r.over_eq, and use the identity direct-image comparison.
This defines its ordinary isomorphism, with exactly SupportNormalization. Closed direct
image is exact and preserves K-injective complexes, since closed inverse image is exact.
Resolve the regular module on the diagonal by a K-injective resolution and push it forward.
Its further pushforward by f is the original resolution by Delta f = id. Consequently
the full right-derived unit on the supported source is invertible, giving t.acyclic.

Finally transpose the asserted equation through the scalar adjunction on the base.
The two endpoint normalizations replace their transposes by the actual coefficient
maps in degree zero. The full-unit normalization of s, evaluated on the single
supported complex, moves the derived unit across the coefficient restriction square.
The remaining equation is naturality of ordinary direct-image composition with
respect to the coefficient map. Both ordinary source isomorphisms have this specified
composition normalization, so it holds before deriving. Injectivity of the scalar Hom
equivalence proves the equation. This uses no line, class, trace, projective-line
cohomology, quotient arithmetic, or flatness of the scalar map. Empty schemes and
zero coefficient rings obey the same unit and composition equations.
-/
theorem diagonal_supported_scalar_source
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (c : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (s : RestrictionSquare a f R (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f)))
    (r : DiagonalTrace.NormalizedSource (CondensedRing.lowerStar Λ f) R
      (source Λ Y) (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (diagonalImmersion Y ≫ f = 𝟙 _) (SupportNormalization Λ Y f)) :
    ∃ e : Endpoint a (source Λ Y) (source Λ' Y)
        (supportMap a Y c.semilinear.hom).hom,
      ∃ t : DiagonalTrace.NormalizedSource (CondensedRing.lowerStar Λ' f)
          (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))
          (source Λ' Y) (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
          (diagonalImmersion Y ≫ f = 𝟙 _) (SupportNormalization Λ' Y f),
        (derivedScalars a (ProjectiveLine Y)).map r.hom ≫ (s.mate a).app _ ≫
          (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f)).R.map e.iso.hom =
        c.iso.hom ≫ t.hom := by
  have hv := diagonal_supported_ordinary_scalars a Y
    c.semilinear.hom c.semilinear.underlying
  have hflat := diagonal_supported_flat Λ Y
  obtain ⟨e⟩ := endpoint_of_flat_ordinary_unit a (diagonalSurface Y)
    (source Λ Y) (source Λ' Y) (supportMap a Y c.semilinear.hom) hflat hv
  obtain ⟨t⟩ := normalizedSource_nonempty Λ' Y f r.over_eq
  have hw : e.semilinear.hom = supportMap a Y c.semilinear.hom :=
    Mod.hom_ext _ _ e.semilinear.underlying
  refine ⟨e, t, ?_⟩
  unfold RestrictionSquare.mate
  apply source_mate_square (CondensedRing.lowerStar Λ f) (CondensedRing.lowerStar Λ' f)
    (Mod.comap (coefficientMap a (diagonalSurface Y)))
    (Mod.comap (coefficientMap a (ProjectiveLine Y))) R
    (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (CondensedRing.comapLowerStarIso a f) s
    (derivedScalars a (diagonalSurface Y)) (derivedScalars a (ProjectiveLine Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a (diagonalSurface Y)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a (ProjectiveLine Y)))
    e.semilinear.hom c.semilinear.hom e.iso c.iso e.normalization c.normalization r t
  exact map_square_of_eq (CondensedRing.lowerStar Λ f) r.iso.hom
    ((CondensedRing.comapLowerStarIso a f).inv.app (source Λ' Y)) hw
    (ordinary_source_square a Y f r.over_eq r.iso t.iso r.normalization
      t.normalization c.semilinear.hom c.semilinear.underlying)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
