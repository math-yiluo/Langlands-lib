/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.DerivedChangeOfRingsModel
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Flat constant extension and tensor of pro-zero cone towers

Source: Stacks Project, proetale.tex, Tag 099M, transport of the Koszul pro-isomorphism;
sites-cohomology.tex, Tags 06YN and 0941.
(auxiliary; not a blueprint node).

## Main declarations

- `flatConstantTensorFunctor`: termwise flat constant extension and total tensor.
- `flatConstantUnitLimitMap`: the specified strict coaugmentation map to Rlim.
- `flatConstantTensorProZeroCones`: pro-zero transport and unit compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v wA wO a b d
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

namespace CategoryTheory

/-- The existing equivalence writes a strict tower of complexes as a complex of towers.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
abbrev flatConstantTowerComplex {B : Type a} [Category.{b} B] [HasZeroMorphisms B] :=
  (HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse

/-- The canonical map from a strict cone to the total derived inverse limit. It is the
ordinary constant/limit adjunction unit, followed by the strict cone and the derived
comparison η. On a K-injective replacement j it is Q(lim(jα)), as in Stacks 0941.
Source: Stacks 0940--0941
(auxiliary; not a blueprint node). -/
def flatConstantStrictConeMap {B : Type a} [Category.{b} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{d} B]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (U : CochainComplex B ℤ) (Z : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (α : (Functor.const ℕᵒᵖ).obj U ⟶ Z) :
    DerivedCategory.Q.obj U ⟶ RF.obj (DerivedCategory.Q.obj (flatConstantTowerComplex.obj Z)) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (constLimAdj (J := ℕᵒᵖ) (C := B)).unit (.up ℤ)).app U ≫
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map
        (flatConstantTowerComplex.map α)) ≫ η.app (flatConstantTowerComplex.obj Z)

/-- The pointed version of the canonical strict-cone comparison, for any strict functor.
The map is the localization of the chosen strict point followed by the constant/limit
adjunction and the derived comparison, with no choice of a derived-category map.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def flatConstantPointedLimitMap
    {T : Type u} [Category.{v} T] {B : Type a} [Category.{b} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{d} B]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (F : T ⥤ CochainComplex B ℤ) (U : T) (P : CochainComplex B ℤ)
    (ι : P ⟶ F.obj U) (X : ℕᵒᵖ ⥤ T) (α : (Functor.const ℕᵒᵖ).obj U ⟶ X) :
    DerivedCategory.Q.obj P ⟶ RF.obj (DerivedCategory.Q.obj
      (flatConstantTowerComplex.obj (X ⋙ F))) :=
  DerivedCategory.Q.map ι ≫
    flatConstantStrictConeMap RF η (F.obj U) (X ⋙ F)
      ((Functor.constComp ℕᵒᵖ U F).inv ≫ Functor.whiskerRight α F)

/-- A strict cone tower is pro-zero after localization exactly when each level is hit
by a transition that is zero in the derived category. The cone is formed in the
abelian category of towers, retaining all strict transition maps.
Source: Stacks 014E--014F and 0941
(auxiliary; not a blueprint node). -/
def FlatConstantConeProZero {B : Type a} [Category.{b} B] [Abelian B]
    [HasDerivedCategory.{d} B] {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (v : X ⟶ Y) : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
    DerivedCategory.Q.map
      ((CochainComplex.mappingCone (flatConstantTowerComplex.map v)).asFunctor.map
        (homOfLE h).op) = 0

set_option backward.isDefEq.respectTransparency false in
private lemma proZero_of_towerIso
    {B : Type a} [Category.{b} B] [Abelian B] [HasDerivedCategory.{d} B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (e : X ≅ Y)
    (hX : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      DerivedCategory.Q.map (X.map (homOfLE h).op) = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      DerivedCategory.Q.map (Y.map (homOfLE h).op) = 0 := by
  intro n
  obtain ⟨m, h, hm⟩ := hX n
  refine ⟨m, h, ?_⟩
  apply (cancel_epi (DerivedCategory.Q.map (e.hom.app (op m)))).1
  rw [← DerivedCategory.Q.map_comp, ← e.hom.naturality,
    DerivedCategory.Q.map_comp, hm, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private lemma coneComparison_fst
    {B : Type a} [Category.{b} B] [Abelian B]
    {D : Type u} [Category.{v} D] [Abelian D]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (E : B ⥤ D) [E.Additive] (r : ℤ) :
    ((CochainComplex.mappingCone.mapHomologicalComplexIso f E).hom.f r) ≫
      (CochainComplex.mappingCone.fst ((E.mapHomologicalComplex (.up ℤ)).map f)).1.v
        r (r + 1) rfl = E.map ((CochainComplex.mappingCone.fst f).1.v r (r + 1) rfl) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' f E r
    (r + 1) rfl).hom ≫ _ = _
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private lemma coneComparison_snd
    {B : Type a} [Category.{b} B] [Abelian B]
    {D : Type u} [Category.{v} D] [Abelian D]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (E : B ⥤ D) [E.Additive] (r : ℤ) :
    ((CochainComplex.mappingCone.mapHomologicalComplexIso f E).hom.f r) ≫
      (CochainComplex.mappingCone.snd ((E.mapHomologicalComplex (.up ℤ)).map f)).v
        r r (add_zero r) = E.map ((CochainComplex.mappingCone.snd f).v r r (add_zero r)) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' f E r
    (r + 1) rfl).hom ≫ _ = _
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_snd_v,
    CochainComplex.mappingCone.inr_f_snd_v, comp_zero, zero_add]
  exact Category.comp_id _

private def levelConeTower
    {B : Type a} [Category.{b} B] [Abelian B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    ℕᵒᵖ ⥤ CochainComplex B ℤ where
  obj n := CochainComplex.mappingCone (f.app n)
  map {m n} t := CochainComplex.mappingCone.map (f.app m) (f.app n)
    (X.map t) (Y.map t) (f.naturality t).symm
  map_id n := by
    simpa only [Functor.map_id] using CochainComplex.mappingCone.map_id (f.app n)
  map_comp {m n k} t s := by
    simpa only [Functor.map_comp] using CochainComplex.mappingCone.map_comp
      (f.app m) (f.app n) (f.app k) (X.map t) (Y.map t)
      (f.naturality t).symm (X.map s) (Y.map s) (f.naturality s).symm

set_option backward.isDefEq.respectTransparency false in
private def levelConeTowerIso
    {B : Type a} [Category.{b} B] [Abelian B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    (CochainComplex.mappingCone (flatConstantTowerComplex.map f)).asFunctor ≅
      levelConeTower f :=
  NatIso.ofComponents (fun n ↦ CochainComplex.mappingCone.mapHomologicalComplexIso
    (flatConstantTowerComplex.map f) ((evaluation ℕᵒᵖ B).obj n)) (by
      intro m n t
      ext r
      apply CochainComplex.mappingCone.ext_to _ r (r + 1) rfl
      · simp only [HomologicalComplex.comp_f, Category.assoc]
        dsimp only [levelConeTower]
        simp only [CochainComplex.mappingCone.map,
          CochainComplex.mappingCone.desc_f,
          CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
          Preadditive.add_comp, Category.assoc,
          CochainComplex.mappingCone.inl_v_fst_v,
          CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero, Category.comp_id]
        erw [coneComparison_fst]
        rw [← Category.assoc]
        erw [coneComparison_fst]
        exact ((CochainComplex.mappingCone.fst
          (flatConstantTowerComplex.map f)).1.v r (r + 1) rfl).naturality t
      · simp only [HomologicalComplex.comp_f, Category.assoc]
        dsimp only [levelConeTower]
        simp only [CochainComplex.mappingCone.map,
          CochainComplex.mappingCone.desc_f,
          CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
          Preadditive.add_comp, Category.assoc,
          CochainComplex.mappingCone.inl_v_snd_v,
          CochainComplex.mappingCone.inr_f_snd_v, comp_zero, zero_add, Category.comp_id]
        erw [coneComparison_snd]
        rw [← Category.assoc]
        erw [coneComparison_snd]
        exact ((CochainComplex.mappingCone.snd
          (flatConstantTowerComplex.map f)).v r r (add_zero r)).naturality t)

private lemma mapBifunctorMap_id_zero
    {B : Type a} [Category.{b} B] [Preadditive B]
    {D : Type u} [Category.{v} D] [Preadditive D]
    (F : B ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ M : B, (F.obj M).PreservesZeroMorphisms]
    (P K L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor P K F (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor P L F (.up ℤ)] :
    HomologicalComplex.mapBifunctorMap (𝟙 P) (0 : K ⟶ L) F (.up ℤ) = 0 := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := K) (F := F) (c := .up ℤ)
  intro p q hpq
  simp only [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.zero_f_apply,
    Functor.map_zero, comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private def levelConeTower_mapBifunctorIso
    {B : Type a} [Category.{b} B] [Abelian B]
    {D : Type u} [Category.{v} D] [Abelian D]
    (F : B ⥤ B ⥤ D) [F.Additive] [∀ M : B, (F.obj M).Additive]
    [∀ K L : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    (P : CochainComplex B ℤ) {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    levelConeTower f ⋙ (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P ≅
      levelConeTower (Functor.whiskerRight f
        ((Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P)) :=
  NatIso.ofComponents (fun n ↦ CochainComplex.mapBifunctorMappingCone₂Iso P (f.app n) F)
    (by
      intro m n t
      exact CochainComplex.mapBifunctorMappingCone₂Iso_hom_naturality
        F (𝟙 P) (f.app m) (f.app n) (X.map t) (Y.map t) (f.naturality t).symm)

set_option backward.isDefEq.respectTransparency false in
private lemma localizedZero_map
    {B : Type a} [Category.{b} B] [Abelian B] [HasDerivedCategory.{wA} B]
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory.{wO} D]
    (F : CochainComplex B ℤ ⥤ CochainComplex D ℤ) [F.PreservesZeroMorphisms]
    (hF : ∀ {K L : CochainComplex B ℤ} (f : K ⟶ L), QuasiIso f → QuasiIso (F.map f))
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (hf : DerivedCategory.Q.map f = 0) :
    DerivedCategory.Q.map (F.map f) = 0 := by
  let G := F ⋙ (DerivedCategory.Q : CochainComplex D ℤ ⥤ _)
  have hG : (HomologicalComplex.quasiIso B (.up ℤ)).IsInvertedBy G := by
    intro K L f hf
    have : QuasiIso (F.map f) := hF f hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (F.map f)))
  let ε := Localization.fac G hG
    (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)
  have hn := ε.hom.naturality f
  have hz := ε.hom.naturality (0 : K ⟶ L)
  dsimp only [G, Functor.comp_map] at hn hz
  rw [hf] at hn
  simp only [DerivedCategory.Q.map_zero, F.map_zero, comp_zero] at hz
  apply (cancel_epi (ε.hom.app K)).1
  rw [← hn, hz, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private lemma flatConstantConeProZero_map_localized
    {B : Type a} [Category.{b} B] [Abelian B] [HasDerivedCategory.{wA} B]
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory.{wO} D]
    (F : CochainComplex B ℤ ⥤ CochainComplex D ℤ) [F.PreservesZeroMorphisms]
    (hF : ∀ {K L : CochainComplex B ℤ} (g : K ⟶ L), QuasiIso g → QuasiIso (F.map g))
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y)
    (hf : FlatConstantConeProZero.{a, b, wA} f)
    (e : levelConeTower f ⋙ F ≅ levelConeTower (Functor.whiskerRight f F)) :
    FlatConstantConeProZero.{u, v, wO} (Functor.whiskerRight f F) := by
  apply proZero_of_towerIso
    (e ≪≫ (levelConeTowerIso (Functor.whiskerRight f F)).symm)
  have hlevel := proZero_of_towerIso (levelConeTowerIso f) hf
  intro n
  obtain ⟨m, h, hm⟩ := hlevel n
  refine ⟨m, h, ?_⟩
  exact localizedZero_map F hF ((levelConeTower f).map (homOfLE h).op) hm

set_option backward.isDefEq.respectTransparency false in
private lemma proZero_derivedEvaluation
    {B : Type a} [Category.{b} B] [Abelian B]
    [HasDerivedCategory.{d} B] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (E : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ DerivedCategory B))
    (ε : DerivedCategory.Q ⋙ E ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex B ℤ) (DerivedCategory B)).obj
          DerivedCategory.Q)
    (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (hK : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      DerivedCategory.Q.map (K.asFunctor.map (homOfLE h).op) = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (E.obj (DerivedCategory.Q.obj K)).map (homOfLE h).op = 0 := by
  intro n
  obtain ⟨m, h, hm⟩ := hK n
  refine ⟨m, h, ?_⟩
  apply (cancel_mono ((ε.app K).hom.app (op n))).1
  have hn := (ε.app K).hom.naturality (homOfLE h).op
  dsimp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj,
    Functor.comp_map] at hn
  rw [hn]
  change (ε.app K).hom.app (op m) ≫ DerivedCategory.Q.map
    (K.asFunctor.map (homOfLE h).op) = 0 ≫ _
  rw [hm, comp_zero, zero_comp]

private lemma rightDerived_map_isIso
    {B : Type a} [Category.{b} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{d} B] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (R₀ R₁ : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η₀ : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R₀)
    (η₁ : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R₁)
    (h₀ : R₀.IsRightDerivedFunctor η₀ (HomologicalComplex.quasiIso _ (.up ℤ)))
    (h₁ : R₁.IsRightDerivedFunctor η₁ (HomologicalComplex.quasiIso _ (.up ℤ)))
    {K L : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : K ⟶ L)
    (hf : IsIso (R₀.map (DerivedCategory.Q.map f))) :
    IsIso (R₁.map (DerivedCategory.Q.map f)) := by
  let := h₀
  let := h₁
  let χ := Functor.rightDerivedUnique R₀ R₁ η₀ η₁
    (HomologicalComplex.quasiIso _ (.up ℤ))
  exact (NatIso.isIso_map_iff χ (DerivedCategory.Q.map f)).1 hf

private lemma ringedLimit_proZero_isIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wO} (ringedSiteModules.{max u v, max u v, v, u} R)]
    [HasDerivedCategory.{wO} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v, max u v, v, u} R)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{max u v, max u v, v, u} R) ⥤
      DerivedCategory (ringedSiteModules.{max u v, max u v, v, u} R))
    (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{max u v, max u v, v, u} R) ⥤
      ringedSiteModules.{max u v, max u v, v, u} R).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)))
    {X Y : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max u v, max u v, v, u} R) ℤ}
    (f : X ⟶ Y) (hf : FlatConstantConeProZero.{_, _, wO} f) :
    IsIso (RF.map (DerivedCategory.Q.map (flatConstantTowerComplex.map f))) := by
  obtain ⟨R₀, η₀, h₀, _, _, hs, hp, E, ε, p, δ, _, _, _, _, _, hi⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients.{wO, u, v, max u v} J R hcomm
  apply rightDerived_map_isIso.{(max u v) + 1, max u v, wO}
    (B := ringedSiteModules.{max u v, max u v, v, u} R) R₀ RF η₀ η h₀ hRF
    (flatConstantTowerComplex.map f)
  apply hi (flatConstantTowerComplex.obj X) (flatConstantTowerComplex.obj Y)
    (flatConstantTowerComplex.map f)
  exact proZero_derivedEvaluation.{(max u v) + 1, max u v, wO}
    (B := ringedSiteModules.{max u v, max u v, v, u} R) E ε
    (CochainComplex.mappingCone (flatConstantTowerComplex.map f)) hf

-- Use the cone APIs without expanding their strict tower data during specialization.
attribute [local irreducible] levelConeTower FlatConstantConeProZero
  flatConstantPointedLimitMap flatConstantStrictConeMap

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Reuse the existing coefficient-forgetful sheaf-composition instance.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
instance flatConstantHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  inferInstance

attribute [-instance] flatConstantHasSheafCompose
attribute [local instance] flatConstantHasSheafCompose

variable (A : Type (max u v)) [CommRing A]
  {O : Sheaf J CommRingCat.{max u v}} (φ : realizationRing J A ⟶ O)

/-- Reuse the existing abelian structure of the module-sheaf category.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance flatConstantModulesAbelian :
    Abelian (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :=
  inferInstance

attribute [-instance] flatConstantModulesAbelian
attribute [local instance] flatConstantModulesAbelian

/-- Reuse ordinary strict inverse limits in the module-sheaf category.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
instance flatConstantModulesLimits :
    HasLimitsOfShape ℕᵒᵖ (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :=
  inferInstance

attribute [-instance] flatConstantModulesLimits
attribute [local instance] flatConstantModulesLimits

variable
  [HasDerivedCategory.{wO} (SheafOfModules.{max u v}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))]

/-- Specialize the existing canonical scalar-extension model to the constant ring sheaf,
using the standard source localization. No source localization is additional input.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
noncomputable instance flatConstantSourceHasDerivedCategory :
    HasDerivedCategory
      (SheafOfModules (SheafOfModules.derivedChangeRingIndependentCoefficients J
        (realizationRing J A))) :=
  HasDerivedCategory.standard (realizationModules J A)

/-- The recorded canonical extension model, at the standard source localization.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
noncomputable def flatConstantExtensionModel
    (φ : realizationRing J A ⟶ O) :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, max u v,
      (max u v) + 1, wO} φ :=
  SheafOfModules.canonicalDerivedChangeOfRingsModel.{u, v, max u v, (max u v) + 1, wO} φ

/-- Ordinary E(M) = O ⊗_R underline M, with its prescribed O-action. The existing
canonical model fixes objects and maps to sheafified scalar tensor by obj_eq and map_eq.
Source: Stacks 03EK and 099M
(auxiliary; not a blueprint node). -/
abbrev flatConstantExtension
    (φ : realizationRing J A ⟶ O) :
    ModuleCat.{max u v} A ⥤ SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O) :=
  commutativeSiteConstantModuleFunctor J A ⋙ (flatConstantExtensionModel J A φ).E

/-- Reuse the existing monoidal structure on total cochain tensor.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
instance flatConstantCochainMonoidal :
    MonoidalCategory (CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :=
  inferInstance

attribute [-instance] flatConstantCochainMonoidal
attribute [local instance] flatConstantCochainMonoidal

/-- Use the same cochain tensor data for whiskering and the unitors.
Source: Stacks 06YN (auxiliary; not a blueprint node). -/
instance flatConstantCochainMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :=
  (flatConstantCochainMonoidal (J := J) (O := O)).toMonoidalCategoryStruct

attribute [-instance] flatConstantCochainMonoidalStruct
attribute [local instance] flatConstantCochainMonoidalStruct

/-- Reuse the existing additivity witness for ordinary constant extension.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
instance flatConstantExtensionAdditive (φ : realizationRing J A ⟶ O) :
    (flatConstantExtension J A φ).Additive :=
  inferInstance

attribute [-instance] flatConstantExtensionAdditive
attribute [local instance] flatConstantExtensionAdditive

attribute [local irreducible] flatConstantExtensionModel

/-- Termwise constant extension followed by the direct-sum total tensor with P.
Source: Stacks 06YN and 099M
(auxiliary; not a blueprint node). -/
def flatConstantTensorFunctor
    (φ : realizationRing J A ⟶ O)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :
    CochainComplex (ModuleCat.{max u v} A) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ :=
  (flatConstantExtension J A φ).mapHomologicalComplex (.up ℤ) ⋙ tensorLeft P

/-- The actual constant section of the constant module A.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def flatConstantRegularSection (U : Cᵒᵖ) (x : A) :
    ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A)).val.obj U :=
  (toSheafify J ((siteConstantModulePresheafGeneral (C := C) A).obj
    (ModuleCat.of A A)).presheaf).app U x

/-- The normalization of the canonical coefficient-unit isomorphism: multiplication
s ⊗ underline a ↦ s φ(a). Thus the unit used below is determined on local pure tensors.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def FlatConstantUnitNormalized
    (φ : realizationRing J A ⟶ O)
    (i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) : Prop :=
  ∀ (U : Cᵒᵖ) (s : O.obj.obj U) (x : A),
    ((eqToHom ((flatConstantExtensionModel J A φ).obj_eq
      ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A))).symm ≫ i.hom).val.app U)
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
          ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A))).presheaf).app U
            (s ⊗ₜ[(realizationRing J A).obj.obj U, (φ.hom.app U).hom]
              flatConstantRegularSection J A U x)) =
      s * (φ.hom.app U) ((realizationRingUnit J A).app U x)

/-- P → P ⊗ E(A[0]) is the inverse ordinary tensor unitor and the inverse coefficient
multiplication isomorphism, extended as a degree-zero complex. This is a strict chain map.
Source: Stacks 03EK and 099M
(auxiliary; not a blueprint node). -/
def flatConstantTensorUnit
    (φ : realizationRing J A ⟶ O)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ)
    (i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :
    P ⟶ (flatConstantTensorFunctor J A φ P).obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
        (ModuleCat.of A A)) :=
  (ρ_ P).inv ≫ P ◁
    (((HomologicalComplex.singleMapHomologicalComplex
      (flatConstantExtension J A φ) (.up ℤ) 0).app (ModuleCat.of A A)) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso i).inv

namespace FlatConstantUnitProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev R :=
  SheafOfModules.derivedChangeRingIndependentCoefficients J (realizationRing J A)

private abbrev M := (commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A)

private def linearUnit :
    (siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A A) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj (M J A).val := by
  let := (realizationRingUnit_locallyBijective J A).1
  let := (realizationRingUnit_locallyBijective J A).2
  exact (PresheafOfModules.sheafificationAdjunction (realizationRingUnit J A)).unit.app _

private def regularLinear :
    (siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A A) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj
        (SheafOfModules.unit (R J A)).val where
  app U := ModuleCat.ofHom
    (X := ((siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A A)).obj U)
    (Y := ((PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj
      (SheafOfModules.unit (R J A)).val).obj U)
    { toFun := fun x ↦ (realizationRingUnit J A).app U x
      map_add' := ((realizationRingUnit J A).app U).hom.map_add
      map_smul' := fun r x ↦ ((realizationRingUnit J A).app U).hom.map_mul r x }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact NatTrans.naturality_apply (realizationRingUnit J A) f x

private def regularHom : M J A ⟶ SheafOfModules.unit (R J A) := by
  let := (realizationRingUnit_locallyBijective J A).1
  let := (realizationRingUnit_locallyBijective J A).2
  exact ((PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit J A)).homEquiv _ _).symm (regularLinear J A)

set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{max u v} C] in
private lemma regularHom_section (U : Cᵒᵖ) (x : A) :
    (regularHom J A).val.app U (flatConstantRegularSection J A U x) =
      (realizationRingUnit J A).app U x := by
  let := (realizationRingUnit_locallyBijective J A).1
  let := (realizationRingUnit_locallyBijective J A).2
  have h := ((PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit J A)).homEquiv
      ((siteConstantModulePresheafGeneral (C := C) A).obj (ModuleCat.of A A))
      (SheafOfModules.unit (R J A))).apply_symm_apply (regularLinear J A)
  exact congrArg (fun f ↦ f.app U x) h

private def oneSection : (M J A).sections :=
  ⟨fun U ↦ flatConstantRegularSection J A U 1,
    fun {_ _} f ↦ (NatTrans.naturality_apply
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) A).obj
        (ModuleCat.of A A)).presheaf) f (1 : A)).symm⟩

private def regularInv : SheafOfModules.unit (R J A) ⟶ M J A :=
  (SheafOfModules.unitHomEquiv _).symm (oneSection J A)

omit [EssentiallySmall.{max u v} C] [J.WEqualsLocallyBijective AddCommGrpCat] in
private lemma regularInv_apply (U : Cᵒᵖ) (x : (R J A).obj.obj U) :
    (regularInv J A).val.app U x = x • flatConstantRegularSection J A U 1 := rfl

set_option backward.isDefEq.respectTransparency false in
private def regularIso : M J A ≅ SheafOfModules.unit (R J A) where
  hom := regularHom J A
  inv := regularInv J A
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply sheafify_hom_ext J _ _ (M J A).isSheaf
    ext U x
    change A at x
    change (regularInv J A).val.app U
      ((regularHom J A).val.app U (flatConstantRegularSection J A U x)) = _
    rw [regularHom_section]
    change (realizationRingUnit J A).app U x • flatConstantRegularSection J A U 1 =
      flatConstantRegularSection J A U x
    have h := ((linearUnit J A).app U).hom.map_smul x (1 : A)
    change flatConstantRegularSection J A U (x * 1) =
      (realizationRingUnit J A).app U x • flatConstantRegularSection J A U 1 at h
    simpa only [mul_one] using h.symm
  inv_hom_id := by
    apply (SheafOfModules.unitHomEquiv _).injective
    ext U
    change (regularHom J A).val.app U
      ((regularInv J A).val.app U (1 : (R J A).obj.obj U)) =
        (1 : (R J A).obj.obj U)
    rw [regularInv_apply, one_smul, regularHom_section, map_one]

private def scalarUnitPresheafIso :
    SheafOfModules.changeOfRingsPresheaf.{v, u, max u v} φ
      (SheafOfModules.unit (R J A)) ≅
      (SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O)).val :=
  PresheafOfModules.isoMk (fun U ↦ by
    letI := (φ.hom.app U).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      ((realizationRing J A).obj.obj U) (O.obj.obj U) (O.obj.obj U)).toModuleIso) (by
        intro U V f
        let := (φ.hom.app U).hom.toAlgebra
        let := (φ.hom.app V).hom.toAlgebra
        apply ModuleCat.ExtendScalars.hom_ext
        intro r
        have ht := Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap φ
            (SheafOfModules.unit (R J A)) f) (1 : O.obj.obj U) r
        change SheafOfModules.changeOfRingsMap φ (SheafOfModules.unit (R J A)) f
          ((1 : O.obj.obj U) ⊗ₜ[(realizationRing J A).obj.obj U, (φ.hom.app U).hom] r) = _ at ht
        change (TensorProduct.AlgebraTensorModule.rid
          ((realizationRing J A).obj.obj V) (O.obj.obj V) (O.obj.obj V))
            (SheafOfModules.changeOfRingsMap φ (SheafOfModules.unit (R J A)) f
              ((1 : O.obj.obj U) ⊗ₜ[(realizationRing J A).obj.obj U, (φ.hom.app U).hom] r)) = _
        rw [ht]
        change (φ.hom.app V) ((realizationRing J A).obj.map f r) *
          (O.obj.map f (1 : O.obj.obj U)) =
          O.obj.map f ((φ.hom.app U r) * (1 : O.obj.obj U))
        simp only [map_one, mul_one]
        exact NatTrans.naturality_apply φ.hom f r)

private def scalarUnitIso :
    SheafOfModules.changeOfRings.{v, u, max u v} φ (SheafOfModules.unit (R J A)) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O) := by
  let S := SheafOfModules.derivedChangeRingIndependentCoefficients J O
  let F := PresheafOfModules.sheafification.{max u v} (R := S) (𝟙 S.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v} (R := S) (𝟙 S.obj)
  let e : (SheafOfModules.unit S).val ≅
      (SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars (𝟙 S.obj)).obj
        (SheafOfModules.unit S) := Iso.refl _
  exact F.mapIso (scalarUnitPresheafIso J A φ ≪≫ e) ≪≫
    (asIso adj.counit).app (SheafOfModules.unit S)

private def coefficientIso :
    (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O) :=
  (flatConstantExtensionModel J A φ).E.mapIso (regularIso J A) ≪≫
    eqToIso ((flatConstantExtensionModel J A φ).obj_eq (SheafOfModules.unit (R J A))) ≪≫
      scalarUnitIso J A φ

end FlatConstantUnitProof

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory.{wO} (SheafOfModules.{max u v}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J O))] in
private lemma flatConstantTensor_preservesQuasiIso
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := O) P)
    {K L : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ}
    (f : K ⟶ L) (hf : QuasiIso f) : QuasiIso (P ◁ f) := by
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  have hc := hP (CochainComplex.mappingCone f)
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
  have ht : (P ⊗ CochainComplex.mappingCone f).Acyclic :=
    HomologicalComplex.Acyclic.of_iso hc (β_ (CochainComplex.mappingCone f) P)
  exact HomologicalComplex.Acyclic.of_iso ht
    (CochainComplex.mapBifunctorMappingCone₂Iso P f (curriedTensor _))

private lemma flatConstantConeProZero_tensor
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := O) P)
    {X Y : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ}
    (f : X ⟶ Y) (hf : FlatConstantConeProZero.{(max u v) + 1, max u v, wO} f) :
    FlatConstantConeProZero.{(max u v) + 1, max u v, wO}
      (Functor.whiskerRight f (tensorLeft P)) := by
  have : (tensorLeft P).PreservesZeroMorphisms := by
    constructor
    intro K L
    change HomologicalComplex.mapBifunctorMap (𝟙 P) (0 : K ⟶ L)
      (curriedTensor _) (.up ℤ) = 0
    exact mapBifunctorMap_id_zero (curriedTensor _) P K L
  let e : levelConeTower f ⋙ tensorLeft P ≅
      levelConeTower (Functor.whiskerRight f (tensorLeft P)) :=
    levelConeTower_mapBifunctorIso (curriedTensor _) P f
  exact flatConstantConeProZero_map_localized.{(max u v) + 1, max u v, wO, wO,
    (max u v) + 1, max u v} (tensorLeft P)
    (fun g hg ↦ flatConstantTensor_preservesQuasiIso (C := C) (O := O) J P hP g hg)
    f hf e

-- Keep total tensor and localization data folded while assembling their proved APIs.
attribute [local irreducible] flatConstantTensorFunctor
  FlatConstantUnitProof.coefficientIso flatConstantTensorUnit FlatConstantUnitNormalized

end CategoryTheory
