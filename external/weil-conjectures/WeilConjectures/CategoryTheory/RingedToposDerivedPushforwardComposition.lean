/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.RingedToposMorphism
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Composition of unbounded derived direct images of ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

section Generic

private theorem hom_localization_bijective
    {C : Type u₁} {D : Type u₂} {DC : Type u₃} {DD : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} DC] [Category.{v₄} DD]
    {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F)
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ DC) [Q.IsLocalization W] (QD : D ⥤ DD)
    (P : ObjectProperty C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), P X' ∧ IsIso (Q.map s))
    (hinv : ∀ {X Y : C}, P X → P Y → ∀ s : X ⟶ Y,
      IsIso (Q.map s) → IsIso (QD.map (G.map s)))
    (K : C) (hK : P K) (I : D)
    (hQI : ∀ X : D, Function.Bijective (QD.map : (X ⟶ I) → _)) :
    Function.Bijective (Q.map : (K ⟶ F.obj I) → _) := by
  constructor
  · intro a b hab
    obtain ⟨T, s, hs, heq⟩ := (W.map_eq_iff_precomp Q a b).mp hab
    obtain ⟨A, z, hA, hz⟩ := hres T
    let := hz
    let : IsIso (Q.map s) := Localization.inverts Q W s hs
    let t := z ≫ s
    have ht : IsIso (Q.map t) := by dsimp [t]; rw [Functor.map_comp]; infer_instance
    let : IsIso (QD.map (G.map t)) := hinv hA hK t ht
    have heq' : t ≫ a = t ≫ b := by dsimp [t]; rw [Category.assoc, heq, Category.assoc]
    apply (adj.homEquiv K I).symm.injective
    apply (hQI (G.obj K)).injective
    apply (cancel_epi (QD.map (G.map t))).mp
    rw [← QD.map_comp, ← QD.map_comp,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm, heq']
  · intro a
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q W a
    obtain ⟨T, s, hs, b, rfl⟩ := φ.cases
    let : IsIso (Q.map s) := Localization.inverts Q W s hs
    obtain ⟨A, z, hA, hz⟩ := hres T
    let := hz
    let t := z ≫ s
    let b' := z ≫ b
    have ht : IsIso (Q.map t) := by dsimp [t]; rw [Functor.map_comp]; infer_instance
    let := ht
    let : IsIso (QD.map (G.map t)) := hinv hA hK t ht
    let c := (adj.homEquiv A I).symm b'
    obtain ⟨d, hd⟩ := (hQI (G.obj K)).surjective
      (inv (QD.map (G.map t)) ≫ QD.map c)
    have htd : G.map t ≫ d = c := by
      apply (hQI (G.obj A)).injective
      rw [Functor.map_comp, hd, IsIso.hom_inv_id_assoc]
    have hta : t ≫ (adj.homEquiv K I) d = b' := by
      rw [← adj.homEquiv_naturality_left, htd]
      exact (adj.homEquiv A I).apply_symm_apply b'
    refine ⟨(adj.homEquiv K I) d, ?_⟩
    apply (cancel_epi (Q.map t)).mp
    rw [← Q.map_comp, hta]
    rw [hφ]
    dsimp [t, b', MorphismProperty.RightFraction.map]
    simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
private theorem postcomp_bijective
    {C DC : Type*} [Category* C] [Category* DC] (Q : C ⥤ DC)
    {X Y Z : C} (j : Y ⟶ Z) [IsIso (Q.map j)]
    (hY : Function.Bijective (Q.map : (X ⟶ Y) → _))
    (hZ : Function.Bijective (Q.map : (X ⟶ Z) → _)) :
    Function.Bijective (fun a : X ⟶ Y ↦ a ≫ j) := by
  constructor
  · intro a b hab
    apply hY.injective
    apply (cancel_mono (Q.map j)).mp
    simpa only [← Q.map_comp] using congrArg Q.map hab
  · intro b
    obtain ⟨a, ha⟩ := hY.surjective (Q.map b ≫ inv (Q.map j))
    refine ⟨a, hZ.injective ?_⟩
    simp only [Q.map_comp, ha, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Two resolving pullback adjunctions detect acyclicity of a right-adjoint image.

The right-fraction hom comparisons identify postcomposition with the given localized
isomorphism on every good test object; resolving arbitrary objects then applies Yoneda. -/
theorem isIso_map_of_adjoints
    {A B E DA DB DE : Type*}
    [Category* A] [Category* B] [Category* E]
    [Category* DA] [Category* DB] [Category* DE]
    {FL : B ⥤ A} {FR : A ⥤ B} (af : FL ⊣ FR)
    {GL : E ⥤ B} {GR : B ⥤ E} (ag : GL ⊣ GR)
    (WB : MorphismProperty B) [WB.HasRightCalculusOfFractions]
    (WE : MorphismProperty E) [WE.HasRightCalculusOfFractions]
    (QA : A ⥤ DA) (QB : B ⥤ DB) [QB.IsLocalization WB]
    (QE : E ⥤ DE) [QE.IsLocalization WE]
    (PB : ObjectProperty B) (PE : ObjectProperty E)
    (hresB : ∀ X : B, ∃ (X' : B) (s : X' ⟶ X), PB X' ∧ IsIso (QB.map s))
    (hresE : ∀ X : E, ∃ (X' : E) (s : X' ⟶ X), PE X' ∧ IsIso (QE.map s))
    (hinvf : ∀ {X Y : B}, PB X → PB Y → ∀ s : X ⟶ Y,
      IsIso (QB.map s) → IsIso (QA.map (FL.map s)))
    (hinvg : ∀ {X Y : E}, PE X → PE Y → ∀ s : X ⟶ Y,
      IsIso (QE.map s) → IsIso (QB.map (GL.map s)))
    (hgood : ∀ X : E, PE X → PB (GL.obj X))
    (I : A) (hI : ∀ X : A, Function.Bijective (QA.map : (X ⟶ I) → _))
    (T : B) (hT : ∀ X : B, Function.Bijective (QB.map : (X ⟶ T) → _))
    (j : FR.obj I ⟶ T) [IsIso (QB.map j)] : IsIso (QE.map (GR.map j)) := by
  have htest (K : E) (hK : PE K) :
      Function.Bijective (fun a : QE.obj K ⟶ QE.obj (GR.obj (FR.obj I)) ↦
        a ≫ QE.map (GR.map j)) := by
    have hcompinv : ∀ {X Y : E}, PE X → PE Y → ∀ s : X ⟶ Y,
        IsIso (QE.map s) → IsIso (QA.map ((GL ⋙ FL).map s)) := by
      intro X Y hX hY s hs
      exact hinvf (hgood X hX) (hgood Y hY) (GL.map s) (hinvg hX hY s hs)
    have hloc₁ := hom_localization_bijective (ag.comp af) WE QE QA PE hresE
      hcompinv K hK I hI
    have hloc₂ := hom_localization_bijective ag WE QE QB PE hresE hinvg K hK T hT
    have hlocf := hom_localization_bijective af WB QB QA PB hresB hinvf
      (GL.obj K) (hgood K hK) I hI
    have hb := postcomp_bijective QB j hlocf (hT (GL.obj K))
    have ha : Function.Bijective (fun a : K ⟶ GR.obj (FR.obj I) ↦ a ≫ GR.map j) := by
      have he := (ag.homEquiv K T).bijective.comp
        (hb.comp (ag.homEquiv K (FR.obj I)).symm.bijective)
      convert he using 1
      funext a
      dsimp only [Function.comp_def]
      rw [ag.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have hm : Function.Bijective (fun a : K ⟶ GR.obj (FR.obj I) ↦
        QE.map a ≫ QE.map (GR.map j)) := by
      simpa only [Function.comp_def, Functor.map_comp] using hloc₂.comp ha
    exact (Function.Bijective.of_comp_iff _ hloc₁).mp hm
  have := Localization.essSurj QE WE
  apply isIso_of_yoneda_map_bijective
  intro X
  obtain ⟨K, s, hK, hs⟩ := hresE (QE.objPreimage X)
  have := hs
  let e : QE.obj K ≅ X := asIso (QE.map s) ≪≫ QE.objObjPreimageIso X
  have h := htest K hK
  constructor
  · intro a b hab
    have heq : e.hom ≫ a = e.hom ≫ b := h.injective (by
      simpa only [Category.assoc] using congrArg (fun c ↦ e.hom ≫ c) hab)
    exact (cancel_epi e.hom).mp heq
  · intro b
    obtain ⟨a, ha⟩ := h.surjective (e.hom ≫ b)
    refine ⟨e.inv ≫ a, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun c ↦ e.inv ≫ c) ha

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
omit [HasDerivedCategory A] in
theorem derives (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w}) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  have he := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  obtain ⟨e, he⟩ := he
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom))
  infer_instance
theorem exists_derived [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    ∃ (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
      (η : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (η.app I) := by
  let H := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w}
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  have h := derives F
  have := h.hasPointwiseRightDerivedFunctor
  refine ⟨H.totalRightDerived DerivedCategory.Q W,
    H.totalRightDerivedUnit DerivedCategory.Q W, inferInstance, ?_⟩
  intro I hI
  exact h.isIso_of_isRightDerivedFunctor _ (CochainComplex.KInjectives.mk I)
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w} E]
private theorem composition [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (hFG : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      ∀ (T : CochainComplex B ℤ), T.IsKInjective →
      ∀ (j : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
      ∀ [QuasiIso j], QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j)) :
    ∃ (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
      (RG : DerivedCategory.{w} B ⥤ DerivedCategory.{w} E)
      (RFG : DerivedCategory.{w} A ⥤ DerivedCategory.{w} E)
      (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF)
      (ηg : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RG)
      (ηfg : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RFG),
      RF.IsRightDerivedFunctor ηf (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      RG.IsRightDerivedFunctor ηg (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) ∧
      RFG.IsRightDerivedFunctor ηfg (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηfg.app I)) ∧
      (∀ T : CochainComplex B ℤ, T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : RFG ≅ RF ⋙ RG,
        (∀ M : CochainComplex A ℤ,
          ηfg.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              RG.map (ηf.app M)) ∧
        ∀ I : CochainComplex A ℤ, I.IsKInjective →
        ∀ T : CochainComplex B ℤ, T.IsKInjective →
        ∀ (j : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
        ∀ [QuasiIso j],
        QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηfg.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ RG.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I) := by
  obtain ⟨RF, ηf, hf, hIf⟩ := exists_derived F
  obtain ⟨RG, ηg, hg, hIg⟩ := exists_derived G
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let ηfg : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ RG) :=
    { app := fun M ↦ ηg.app (Fc.obj M) ≫ RG.map (ηf.app M)
      naturality := by
        intro M N a
        dsimp only [Functor.comp_map]
        change DerivedCategory.Q.map (Gc.map (Fc.map a)) ≫
            (ηg.app (Fc.obj N) ≫ RG.map (ηf.app N)) =
          (ηg.app (Fc.obj M) ≫ RG.map (ηf.app M)) ≫ RG.map (RF.map (DerivedCategory.Q.map a))
        have hn := ηg.naturality (Fc.map a)
        have hm := ηf.naturality a
        dsimp only [Functor.comp_map] at hn hm
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← RG.map_comp, hm, RG.map_comp] }
  have hGFI (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (ηg.app (Fc.obj I)) := by
    obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective (Fc.obj I)
    have : QuasiIso j := hj
    have : QuasiIso (Gc.map j) := hFG I hI T hT j
    have : IsIso (ηg.app T) := hIg T hT
    have : IsIso (DerivedCategory.Q.map (Gc.map j)) := inferInstance
    have : IsIso (RG.map (DerivedCategory.Q.map j)) := inferInstance
    have hn := ηg.naturality j
    dsimp only [Functor.comp_map] at hn
    have : IsIso (ηg.app (Fc.obj I) ≫ RG.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (RG.map (DerivedCategory.Q.map j))
  have hIfg (I : CochainComplex A ℤ) (hI : I.IsKInjective) : IsIso (ηfg.app I) := by
    have := hIf I hI
    have := hGFI I hI
    dsimp only [ηfg]
    infer_instance
  have hfg : (RF ⋙ RG).IsRightDerivedFunctor ηfg
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    apply (derives (F ⋙ G)).isRightDerivedFunctor_of_isIso ηfg
    intro X
    exact hIfg X.obj X.property
  refine ⟨RF, RG, RF ⋙ RG, ηf, ηg, ηfg, hf, hg, hfg,
    (fun I hI ↦ ⟨hIf I hI, hIfg I hI⟩), hIg, Iso.refl _, ⟨?_, ?_⟩, ?_⟩
  · intro M
    exact Category.comp_id _
  · intro I hI T hT j hj
    refine ⟨hFG I hI T hT j, ?_⟩
    change (ηg.app (Fc.obj I) ≫ RG.map (ηf.app I)) ≫ 𝟙 _ = _
    rw [Category.comp_id, RG.map_comp]
    have hn := ηg.naturality j
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc (DerivedCategory.Q.map (Gc.map j)), hn]
    simp only [Category.assoc]
    rw [← RG.map_comp_assoc, IsIso.hom_inv_id, RG.map_id, Category.id_comp]
  · intro κ hκ
    apply Iso.ext
    have := hfg
    apply Functor.rightDerived_ext (RF ⋙ RG) ηfg
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    apply NatTrans.ext
    funext M
    simpa [ηfg] using hκ.1 M

omit [HasDerivedCategory A] in
private theorem quasiIso_of_isIso_map
    (G : A ⥤ B) [G.Additive] {I T : CochainComplex A ℤ} (j : I ⟶ T)
    (h : IsIso (DerivedCategory.Qh.{w}.map
      ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map j)))) :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map j) := by
  rw [G.mapHomotopyCategory_map] at h
  exact (HomologicalComplex.mem_quasiIso_iff _).mp
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
      ((DerivedCategory.isIso_Qh_map_iff _).mp h))

end Generic

/-- A K-flat homotopy complex whose terms are flat module sheaves.

The structure keeps the two properties available without unfolding tensor realizations. -/
structure flatKFlat
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (X : HomotopyCategory
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (ComplexShape.up ℤ)) : Prop where
  kflat : CochainComplex.IsKFlatTensor X.as
  flat (n : ℤ) : SheafOfModules.IsFlat (X.as.X n)

/-- Every module homotopy complex admits a flat-term K-flat resolution. -/
theorem flatKFlat_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∀ X, ∃ (P : _) (s : P ⟶ X), flatKFlat J R P ∧ IsIso (DerivedCategory.Qh.{w}.map s) := by
  intro X
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P, s, hP, hflat, hs, _⟩ := CochainComplex.exists_isKFlatResolution X
  have : QuasiIso s := hs
  refine ⟨(HomotopyCategory.quotient _ _).obj P,
    (HomotopyCategory.quotient _ _).map s, ⟨hP, hflat⟩, ?_⟩
  apply (DerivedCategory.isIso_Qh_map_iff _).mpr
  simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff] using hs

private theorem flatKFlat_inverts
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B))]
    (F : ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) [F.Additive]
    (hinv : ∀ (P Q : CochainComplex (ringedSiteModules.{u, u, u, u}
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) ℤ) (s : P ⟶ Q),
        P.IsKFlatTensor → (∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) →
        Q.IsKFlatTensor → (∀ n : ℤ, SheafOfModules.IsFlat (Q.X n)) →
        QuasiIso s → QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    ∀ {X Y}, flatKFlat K B X → flatKFlat K B Y → ∀ s : X ⟶ Y,
      IsIso (DerivedCategory.Qh.{w}.map s) →
        IsIso (DerivedCategory.Qh.{w}.map
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map s)) := by
  intro X Y hX hY s hs
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  have hq : QuasiIso s := by
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using
        (DerivedCategory.isIso_Qh_map_iff _).mp hs
  apply (DerivedCategory.isIso_Qh_map_iff _).mpr
  simpa only [Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff] using hinv P Q s hX.kflat hX.flat hY.kflat hY.flat hq

-- Repeated module localizations and their comparison-unit equations require more elaboration steps.
/-- The total derived module direct images compose canonically, including the normalization
on arbitrary K-injective resolutions of the intermediate direct image.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(auxiliary; not a blueprint node).

The three existential functors and their units are total right derived functors, computed
on K-injectives as asserted by the invertibility clauses. The direct image of the composite
is the composite module functor. The unit equation characterizes the canonical comparison.
The final equation identifies its component with the class of `g_*j`: the comparison units
at `I` and `J` and the inverse of `Q(j)` are precisely the resolution identifications.

Proof plan:
1. Use the tensor module pullback adjunction for each ringed-topos map. Pass termwise to
   homotopy categories. K-injective resolutions exist on each small ringed site by
   prop-pur-kinjective-resolutions-exist. Apply lem-weil-pbc-kinjective-total-derived and
   lem-pc-derived-adjoint-functors to obtain the canonical derived adjunctions, normalized
   by the fraction formula of lem-pc-pre-derived-adjoint-functors-general.
2. The underlying direct images and the structural coefficient actions identify the
   composite module direct image with g_*f_*. Conjugation of this identification gives
   the underived module pullback composition and its composite counit equation.
3. Choose a K-flat resolution with flat terms using lem-pc-kflat-resolution. Pullback
   preserves these representatives. The termwise pullback comparison descends through
   the K-flat localization (lem-weil-pbc-site-derived-tensor-descent) to a natural derived
   pullback composition isomorphism, independently of the resolution.
4. Conjugate that isomorphism through the canonical derived adjunctions to obtain kappa.
   The adjunction hom bijections characterize it and give its inverse and naturality.
5. For a K-injective I and a resolution j:f_*I→J, represent maps into Qg_*f_*I by right
   fractions, and refine the denominator by a K-flat resolution with flat terms.
6. Apply the canonical fraction adjunction formula twice. Naturality of the module
   counits cancels Q(j) against its inverse in D(B). The composite counit equation from
   step 2 identifies the resulting map with the adjunct of Q(g_*j). Hence Q(g_*j) is
   exactly the kappa component under the displayed resolution identifications.
7. Since that component is invertible, the cohomology criterion implies g_*j is a
   quasi-isomorphism. Uniqueness of maps into K-injectives in the derived category gives
   resolution independence; all comparisons are natural. Universal uniqueness of the
   total right derived functor makes the unit characterization unique. No claim that
   f_* preserves K-injectives is used. -/
theorem ringedToposDerivedPushforwardComposition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (R : Sheaf L CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose L (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      R))]
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K)
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (g : RingedToposMorphism.{u} (C := D) (D := E) (J := K) (K := L)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
      ((sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj
      A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            B)))
      (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat.{u}
        RingCat.{u})).obj
        B)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose L (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            R)))
      (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u}
        RingCat.{u})).obj A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose L (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            R)))
      (ηf : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηg : g.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rg)
      (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rgf),
      Rf.IsRightDerivedFunctor ηf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj A)) (ComplexShape.up ℤ)) ∧
      Rg.IsRightDerivedFunctor ηg
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj B)) (ComplexShape.up ℤ)) ∧
      Rgf.IsRightDerivedFunctor ηgf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj A)) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj A)) ℤ),
        I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηgf.app I)) ∧
      (∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u}
        RingCat.{u})).obj B)) ℤ),
        T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : Rgf ≅ Rf ⋙ Rg,
        (∀ (M : CochainComplex (ringedSiteModules.{u, u, u, u}
          ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A)) ℤ),
          ηgf.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              Rg.map (ηf.app M)) ∧
        ∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u}
          ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A)) ℤ),
          I.IsKInjective → ∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K
            (forget₂
            CommRingCat.{u} RingCat.{u})).obj B)) ℤ),
          T.IsKInjective →
          ∀ (j : (f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
          ∀ [QuasiIso j],
          QuasiIso ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηgf.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ Rg.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I) := by
  classical
  let MA := ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
  let MB := ringedSiteModules.{u, u, u, u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
  let ME := ringedSiteModules.{u, u, u, u}
    ((sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have hA := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions J A).1
  have hB := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions K B).1
  let _ := hA
  let _ := hB
  let _ : Abelian.HasKInjectiveResolutions MA := inferInstance
  let _ : Abelian.HasKInjectiveResolutions MB := inferInstance
  apply composition f.modules g.modules
  intro I hI T hT j hj
  obtain ⟨FL, hFL, af, _, hinvf⟩ := f.exists_kFlatPullback J K A B
  obtain ⟨GL, hGL, ag, hgoodg, hinvg⟩ := g.exists_kFlatPullback K L B R
  have hIs : IsIso (DerivedCategory.Qh.{w}.map
      ((HomotopyCategory.quotient MB (ComplexShape.up ℤ)).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hj
  have hmap : IsIso (DerivedCategory.Qh.{w}.map
      ((g.modules.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient MB (ComplexShape.up ℤ)).map j))) :=
    isIso_map_of_adjoints
    (af.mapHomotopyCategory (ComplexShape.up ℤ))
    (ag.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso MB (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso ME (ComplexShape.up ℤ))
    DerivedCategory.Qh.{w} DerivedCategory.Qh.{w} DerivedCategory.Qh.{w}
    (flatKFlat K B) (flatKFlat L R)
    (flatKFlat_resolutions K B) (flatKFlat_resolutions L R)
    (flatKFlat_inverts J K A B FL hinvf)
    (flatKFlat_inverts K L B R GL hinvg)
    (fun X hX ↦ by
      obtain ⟨hK, hF⟩ := hgoodg X.as hX.kflat hX.flat
      exact ⟨hK, hF⟩)
    ((HomotopyCategory.quotient MA (ComplexShape.up ℤ)).obj I)
    (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X I)
    ((HomotopyCategory.quotient MB (ComplexShape.up ℤ)).obj T)
    (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X T)
    ((HomotopyCategory.quotient MB (ComplexShape.up ℤ)).map j)
  exact quasiIso_of_isIso_map g.modules j hmap

end CategoryTheory
