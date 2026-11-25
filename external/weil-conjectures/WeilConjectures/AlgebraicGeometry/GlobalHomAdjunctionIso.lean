/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DQCoheratorDerivedGlobalSections
import WeilConjectures.AlgebraicGeometry.QCqsSheafRHomAdjunction
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.DQCoheratorAdjunction
import WeilConjectures.AlgebraicGeometry.InternalHomMateCounitTransport

/-!
Canonical adjunction and tensor data are pinned by their characterising equations.
 # Canonical global Hom adjunction
Source: Stacks Project, duality.tex, Tag 0B6I (lemma-iso-global-hom).
(blueprint: lem-pc-global-hom-adjunction).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA vC vD vE vB uC uD uE uB
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
section InternalHomMate
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
variable (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D)
  (F : D ⥤ C) (R : C ⥤ D) (p : F ⊣ R)
  (t : tensor D ⋙ F ≅ F.prod F ⋙ tensor C)
  (ex : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (ey : ∀ A L M : D, (A ⟶ J.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (hx : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    ex A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ ex A L M g ≫ d)
  (hy : ∀ (A A' L L' M M' : D) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ J.obj (op L, M)),
    ey A' L' M' (a ≫ g ≫ J.map (b.op, d)) = (a ⊗ₘ b) ≫ ey A L M g ≫ d)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include hx hy in
/-- Transpose evaluation with fixed natural tensor-Hom bijections.
Source: Stacks, Tag 08I3 (blueprint: lem-pc-global-hom-adjunction). -/
private theorem internalHomMate_exists :
    ∃ c : H ⋙ R ⟶ R.op.prod R ⋙ J,
      ∀ (L M : C) (A : D) (α : A ⟶ R.obj (H.obj (op L, M))),
        ey A (R.obj L) (R.obj M) (α ≫ c.app (op L, M)) =
          p.homEquiv _ M (t.hom.app (A, R.obj L) ≫
            (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm α)) := by
  let c (L M : C) : R.obj (H.obj (op L, M)) ⟶ J.obj (op (R.obj L), R.obj M) :=
    (ey _ _ _).symm (p.homEquiv _ M (t.hom.app (_, R.obj L) ≫
      (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm (𝟙 _))))
  have mate (L M : C) (A : D) (α : A ⟶ R.obj (H.obj (op L, M))) :
      ey A (R.obj L) (R.obj M) (α ≫ c L M) =
        p.homEquiv _ M (t.hom.app (A, R.obj L) ≫
          (𝟙 _ ⊗ₘ p.counit.app L) ≫ ex _ L M ((p.homEquiv _ _).symm α)) := by
    have h₁ := hy _ _ _ _ _ _ α (𝟙 (R.obj L)) (𝟙 (R.obj M)) (c L M)
    change ey _ _ _ (α ≫ c L M ≫ J.map (𝟙 _)) = _ at h₁
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₁
    rw [h₁]
    dsimp only [c]
    rw [Equiv.apply_symm_apply, ← p.homEquiv_naturality_left]
    congr 1
    have h₂ := hx _ _ _ _ _ _ (F.map α) (𝟙 L) (𝟙 M)
      ((p.homEquiv _ _).symm (𝟙 (R.obj (H.obj (op L, M)))))
    change ex _ _ _ (F.map α ≫ _ ≫ H.map (𝟙 _)) = _ at h₂
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h₂
    have hp := p.homEquiv_naturality_left_symm α (𝟙 (R.obj (H.obj (op L, M))))
    simp only [Category.comp_id] at hp
    rw [hp]
    dsimp only [Functor.prod_obj] at *
    rw [h₂]
    have ht := t.hom.naturality (X := (A, R.obj L))
      (Y := (R.obj (H.obj (op L, M)), R.obj L)) (α, 𝟙 (R.obj L))
    dsimp at ht
    simp only [CategoryTheory.Functor.map_id] at ht
    rw [← Category.assoc, ht]
    simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]
    congr 2
    simp
  refine ⟨{ app := fun Z ↦ c Z.1.unop Z.2, naturality := ?_ }, mate⟩
  intro Z Z' g
  obtain ⟨L, M⟩ := Z
  obtain ⟨L', M'⟩ := Z'
  obtain ⟨b, d⟩ := g
  dsimp
  apply (ey _ _ _).injective
  rw [mate]
  have hn := hy _ _ _ _ _ _ (𝟙 (R.obj (H.obj (L, M))))
    (R.map b.unop) (R.map d) (c L.unop M)
  simp only [Category.id_comp] at hn
  change ey _ _ _ (c L.unop M ≫ J.map ((R.map b.unop).op, R.map d)) = _ at hn
  rw [hn]
  dsimp only [c]
  rw [Equiv.apply_symm_apply]
  rw [← p.homEquiv_naturality_right, ← p.homEquiv_naturality_left]
  congr 1
  have he := hx _ _ _ _ _ _ (𝟙 (F.obj (R.obj (H.obj (L, M))))) b.unop d
    ((p.homEquiv _ _).symm (𝟙 (R.obj (H.obj (L, M)))))
  simp only [Category.id_comp] at he
  have hp := p.homEquiv_naturality_right_symm (𝟙 (R.obj (H.obj (L, M))))
    (H.map (b, d))
  simp only [Category.id_comp] at hp
  rw [hp]
  dsimp only [Functor.prod_obj] at *
  simp only [Quiver.Hom.op_unop] at he
  rw [he]
  have ht := t.hom.naturality
    (X := (R.obj (H.obj (L, M)), R.obj L'.unop))
    (Y := (R.obj (H.obj (L, M)), R.obj L.unop))
    (𝟙 _, R.map b.unop)
  dsimp at ht
  simp only [CategoryTheory.Functor.map_id] at ht
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
  congr 2
  exact congrArg (fun z ↦ (𝟙 (F.obj (R.obj (H.obj (L, M))))) ⊗ₘ z)
    (p.counit_naturality b.unop).symm

end InternalHomMate

section TensorHomAdjunction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (H : Cᵒᵖ × C ⥤ C)
  (e : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M))
  (h : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ H.obj (op L, M)),
    e A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A L M g ≫ d)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Build the tensor-Hom adjunction from the pinned natural bijections.
Source: Stacks, Tag 08DJ (blueprint: lem-pc-global-hom-adjunction). -/
private def tensorAdjunctionCore (L : C) :
    Adjunction.CoreHomEquiv (tensorRight L) ((Functor.curry.obj H).obj (op L)) where
  homEquiv A M := (e A L M).symm
  homEquiv_naturality_left_symm {A'} {A} {M} a g := by
    change e A' L M (a ≫ g) = (a ▷ L) ≫ e A L M g
    have h' := h _ _ _ _ _ _ a (𝟙 L) (𝟙 _) g
    change e _ _ _ (a ≫ g ≫ H.map (𝟙 _)) = _ at h'
    erw [H.map_id, Category.comp_id] at h'
    erw [Category.comp_id] at h'
    simpa only [tensorHom_id] using h'
  homEquiv_naturality_right g d := by
    apply (e _ _ _).injective
    erw [Equiv.apply_symm_apply]
    have h' := h _ _ _ _ _ _ (𝟙 _) (𝟙 L) d ((e _ _ _).symm g)
    simp only [Category.id_comp, id_tensorHom_id, Equiv.apply_symm_apply] at h'
    exact h'.symm

end TensorHomAdjunction


section LerayNaturality
variable {C : Type uC} {D : Type uD} {E : Type uE} {B : Type uB}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vB} B]
  (R : C ⥤ D) (G : D ⥤ E) (GX : C ⥤ B) (S : B ⥤ E)
  (e : R ⋙ G ≅ GX ⋙ S)
/-- Transport a natural comparison through a Leray isomorphism.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
private theorem lerayNaturality {U U' : C} {V V' : D} (u : U ⟶ U') (v : V ⟶ V')
    (q : R.obj U ⟶ V) (q' : R.obj U' ⟶ V') (h : R.map u ≫ q' = q ≫ v) :
    S.map (GX.map u) ≫ e.inv.app U' ≫ G.map q' =
      e.inv.app U ≫ G.map q ≫ G.map v := by
  have he := e.inv.naturality u
  dsimp only [Functor.comp_map] at he
  rw [← Category.assoc, he, Category.assoc, ← G.map_comp, h, G.map_comp]

end LerayNaturality

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Derived Leray from acyclicity and an exact change of scalar category.
Source: Stacks, Tag 0D5T (blueprint: lem-pc-global-hom-adjunction). -/
private theorem lerayCore
    {C D B E : Type*} [Category* C] [Category* D] [Category* B] [Category* E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ B) (S : B ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ⋙ G ≅ H ⋙ S)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    ∃ c : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅
        H.rightDerivedFunctor ⋙ S.mapDerivedCategory,
      ∀ K : HomotopyCategory C (.up ℤ),
        G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
            G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) ≫
            c.hom.app (DerivedCategory.Qh.obj K) =
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K ≫
              (Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).inv.app K) ≫
            S.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj K) ≫
            S.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app K) := by
  let α : (F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) :=
    Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv
          DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) G.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.rightDerivedFunctorUnit G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom
  let β : (F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (H.rightDerivedFunctor ⋙ S.mapDerivedCategory) :=
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).inv
        DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (H.mapHomotopyCategory (.up ℤ))
        S.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight H.rightDerivedFunctorUnit S.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  have hα : (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
        _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I))
    have h₁ : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := inferInstance
    have h₂ := h I
    dsimp [α]
    infer_instance
  have hβ : (H.rightDerivedFunctor ⋙ S.mapDerivedCategory).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
        _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (β.app ((HomotopyCategory.quotient C (.up ℤ)).obj I))
    have h₁ : IsIso (H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := inferInstance
    dsimp [β]
    infer_instance
  let δ := (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerivedDesc α
    (HomotopyCategory.quasiIso C (.up ℤ))
    (H.rightDerivedFunctor ⋙ S.mapDerivedCategory) β
  have : IsIso δ :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) α
      (HomotopyCategory.quasiIso C (.up ℤ))
      (H.rightDerivedFunctor ⋙ S.mapDerivedCategory) β).mp hβ
  refine ⟨asIso δ, ?_⟩
  intro K
  have hd := Functor.rightDerived_fac_app
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) α
    (HomotopyCategory.quasiIso C (.up ℤ))
    (H.rightDerivedFunctor ⋙ S.mapDerivedCategory) β K
  simp only [α, β, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id] at hd
  have hd' := congrArg
    (fun z ↦ DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) ≫ z) hd
  simp only [Category.assoc] at hd'
  rw [← Category.assoc, ← DerivedCategory.Qh.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hd'
  simpa only [δ, α, β, asIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc] using hd'


/-- Exact restriction along the map on global functions.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalScalarRestriction
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ModuleCat.restrictScalars.{u}
    (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
    (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom).mapDerivedCategory

/-- The normalized Leray comparison with independent module and sheaf localization universes.
Source: Stacks Tags 0D5T and 0B6I. Its derived-unit equation determines the comparison.
(blueprint: lem-sc-mixed-global-sections-direct-image-iso). -/
theorem exists_mixedGlobalSectionsDirectImageIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (c₀ : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        ModuleCat.restrictScalars.{u}
          (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
          (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom)
      (c : schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
        schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f),
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (x : (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj F),
        (c₀.hom.app F).hom x = x) ∧
      (∀ K : HomotopyCategory
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedGlobalSections Y).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
          c.hom.app (DerivedCategory.Qh.obj K) =
        (DerivedCategory.Qh
          (C := ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))).map
          ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
              RingedSpace.globalSectionsFunctor Y.toRingedSpace))
            (ComplexShape.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso c₀.symm
              (ComplexShape.up ℤ)).inv.app K) ≫
          (ModuleCat.restrictScalars.{u}
            (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
            (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
            f.appTop.hom).mapDerivedCategoryFactorsh.inv.app
              (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) ≫
          (schemeGlobalScalarRestriction f).map
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K))
      := by
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let H := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let S := ModuleCat.restrictScalars.{u}
    (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
    (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom
  let c₀ : F ⋙ G ≅ H ⋙ S := Iso.refl _
  obtain ⟨c, hc⟩ := lerayCore F G H S c₀
    (fun I ↦ isIso_directImage_globalSections_unit_on_kInjective f I)
  refine ⟨c₀, c, ?_, hc⟩
  intro M x
  rfl

/-- The canonical derived Leray isomorphism, chosen with its unit compatibility.
Source: Stacks, Tags 0B6I and 0D5T (blueprint: lem-pc-global-hom-adjunction). -/
def mixedGlobalSectionsDirectImageIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
      schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f :=
  Classical.choose (Classical.choose_spec (exists_mixedGlobalSectionsDirectImageIso f))

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same pinned derived adjunction as the canonical base-change map.
Source: Stacks, Tags 079W and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeHomPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The canonical pullback tensor comparison with independent localization universes.
Proof: take the canonical comparison normalized to SingleComplexBaseChange.counit.
On K-flat representatives, tensor, pullback, localization tensor maps and the shared
left-derived counits are invertible. The canonical coordinate equation thus makes
its components invertible. K-flat resolutions and naturality transport invertibility
to arbitrary objects. Package these components as a natural isomorphism.
Source: Stacks Tags 079U and 0B6I
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso). -/
theorem exists_mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    ∃ t : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T),
      IsCanonicalPullbackTensorComparison h (fun K L ↦ t.hom.app (K, L)) := by
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison h
  let c : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ⟶
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
    { app := fun Z ↦ τ Z.1 Z.2
      naturality := fun Z Z' a ↦ hτ.2 Z.1 Z'.1 Z.2 Z'.2 a.1 a.2 }
  obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization h τ hτ
  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) : IsIso (c.app Z) := by
    change IsIso (τ Z.1 Z.2)
    rw [← hm Z.1 Z.2]
    infer_instance
  exact ⟨NatIso.ofComponents (fun Z ↦ asIso (c.app Z))
    (fun a ↦ c.naturality a), hτ⟩

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The pullback tensorator normalized to the shared derived counit.
Source: Stacks Tag 079U. -/
def mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
  Classical.choose (exists_mixedHomTensorPullbackIso h)

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- Naturality of the fixed family, isolated from its representative equation.
Source: Stacks, Tag 08DJ (blueprint: lem-pc-global-hom-adjunction). -/
private theorem schemeHomTensorHom_naturality (X : Scheme.{u})
    (A A' L L' M M' : schemeDerivedCategory X)
    (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M')
    (g : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op L, M)) :
    schemeDerivedTensorHomEquiv X A' L' M'
        (a ≫ g ≫ (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map (b.op, d)) =
      (a ⊗ₘ b) ≫ schemeDerivedTensorHomEquiv X A L M g ≫ d :=
  (Classical.choose_spec (exists_canonicalDerivedTensorHom X)).1 A A' L L' M M' a b d g

attribute [local irreducible] schemeHomPullbackAdjunction mixedHomTensorPullbackIso

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- Existence of the evaluation-mate direct-image internal Hom comparison.
Fixed-data form of the existing `exists_derivedDirectImage_internalHom_comparison`,
using the pinned tensor-Hom family.
All adjunction and tensor data here are fixed, shared with the pullback comparison.
Source: Stacks, Tags 08I3 and 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof: for every test object A transpose a map into Rf_* internal Hom by the
pullback adjunction and tensor-Hom bijection. Pull back A tensor Rf_*L, apply the
counit at L, then evaluation. Transpose back. This is natural in A, so Yoneda
gives the specified map, and naturality in both Hom entries gives the transformation. -/
theorem exists_schemeHomDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ c : derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf,
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op L, M))),
        (schemeDerivedTensorHomEquiv Y) A
          ((schemeDerivedDirectImage f).obj L) ((schemeDerivedDirectImage f).obj M)
            (α ≫ c.app (op L, M)) =
          (schemeHomPullbackAdjunction f).homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
            ((mixedHomTensorPullbackIso f).hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
              (𝟙 ((derivedPullback f).obj A) ⊗ₘ
                (schemeHomPullbackAdjunction f).counit.app L) ≫
              (schemeDerivedTensorHomEquiv X)
                ((derivedPullback f).obj A) L M
                  (((schemeHomPullbackAdjunction f).homEquiv A
                    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
                      (op L, M))).symm α)) := by
  exact @internalHomMate_exists (schemeDerivedCategory X) (schemeDerivedCategory Y)
    inferInstance inferInstance (schemeDerivedTensorMonoidal X) (schemeDerivedTensorMonoidal Y)
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf)
    (derivedPullback f) (schemeDerivedDirectImage f)
    (schemeHomPullbackAdjunction f) (mixedHomTensorPullbackIso f)
    (schemeDerivedTensorHomEquiv X) (schemeDerivedTensorHomEquiv Y)
    (schemeHomTensorHom_naturality X) (schemeHomTensorHom_naturality Y)

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The fixed direct-image internal-Hom comparison also satisfies the mate equation
when the pullback adjunction and tensor iso are transported together. In particular
this applies to the unique change from the composition counit to the original one.
Source: Stacks, Tags 08I3, 06YJ and 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof: tensor-Hom naturality with identity maps in the last two variables gives
naturality of evaluation in its test object. Apply the formal counit-transport
calculation to identify the transported mate with the original mate. The defining
equation of the chosen direct-image comparison then gives the assertion. -/
theorem schemeHomDirectImageComparison_counit_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y) (δ : derivedPullback f ≅ derivedPullback f)
    (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
    (α : A ⟶ (schemeDerivedDirectImage f).obj
      ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op L, M))) :
    let p := (schemeHomPullbackAdjunction f).ofNatIsoLeft δ
    let t := Functor.isoWhiskerLeft (tensor (schemeDerivedCategory Y)) δ.symm ≪≫
      mixedHomTensorPullbackIso f ≪≫
        Functor.isoWhiskerRight (NatIso.prod δ δ) (tensor (schemeDerivedCategory X))
    let c := Classical.choose (exists_schemeHomDirectImageComparison f)
    schemeDerivedTensorHomEquiv Y A
        ((schemeDerivedDirectImage f).obj L) ((schemeDerivedDirectImage f).obj M)
        (α ≫ c.app (op L, M)) =
      p.homEquiv _ M (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
        (𝟙 _ ⊗ₘ p.counit.app L) ≫
          schemeDerivedTensorHomEquiv X _ L M ((p.homEquiv _ _).symm α)) := by
  have hx : ∀ (B B' N Q : schemeDerivedCategory X) (b : B' ⟶ B)
      (g : B ⟶ (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
        (op N, Q)),
      schemeDerivedTensorHomEquiv X B' N Q (b ≫ g) =
        (b ⊗ₘ 𝟙 N) ≫ schemeDerivedTensorHomEquiv X B N Q g := by
    intro B B' N Q b g
    have h := schemeHomTensorHom_naturality X B B' N N Q Q b (𝟙 N) (𝟙 Q) g
    change schemeDerivedTensorHomEquiv X B' N Q
      (b ≫ g ≫ (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map (𝟙 _)) =
      _ at h
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h
  exact ((Classical.choose_spec (exists_schemeHomDirectImageComparison f)) L M A α).trans
    (internalHomMate_counit_transport
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)
      (derivedPullback f) (schemeDerivedDirectImage f) (schemeHomPullbackAdjunction f)
      (mixedHomTensorPullbackIso f) (schemeDerivedTensorHomEquiv X) hx δ L M A α).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- Transporting the pinned adjunction along a counit comparison gives the
representative Hom equation for the new counit. This can be applied to the
original-counit comparison without choosing another adjunction.
Source: Stacks, Tags 079W and 06YJ (blueprint: lem-pc-global-hom-adjunction).
Proof: the transported Hom equivalence precomposes by the comparison iso.
The counit comparison equation replaces that composite by the composition counit.
The recorded representative equation of the legacy adjunction gives the result. -/
theorem schemeHomPullbackAdjunction_counit_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y) (δ : derivedPullback f ≅ derivedPullback f)
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hδ : ∀ N : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ),
      δ.hom.app (DerivedCategory.Qh.obj N) ≫ ε.app N =
        (SingleComplexBaseChange.counit f).app N)
    (N : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ))
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj N ⟶ K) :
    ((schemeHomPullbackAdjunction f).ofNatIsoLeft δ).homEquiv
        (DerivedCategory.Qh.obj N) (DerivedCategory.Qh.obj K)
        (ε.app N ≫ DerivedCategory.Qh.map a) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory
          (.up ℤ)).homEquiv N K a) ≫
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, ← Category.assoc, hδ]
  unfold schemeHomPullbackAdjunction SingleComplexBaseChange.counit
  exact (Classical.choose_spec (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))) N K a

/-- The canonical global direct-image Hom comparison: Leray followed by the
internal-Hom comparison defined by the evaluation mate equation.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : schemeDerivedCategory X) :
    (schemeGlobalScalarRestriction f).obj ((schemeGlobalDerivedHom X).obj (op P, Q)) ⟶
      (schemeGlobalDerivedHom Y).obj
        (op ((schemeDerivedDirectImage f).obj P), (schemeDerivedDirectImage f).obj Q) :=
  (mixedGlobalSectionsDirectImageIso f).inv.app
      ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op P, Q)) ≫
    (schemeDerivedGlobalSections Y).map
      ((Classical.choose (exists_schemeHomDirectImageComparison f)).app (op P, Q))

/-- The global Hom adjunction map is induced by the counit, not an arbitrary iso.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomAdjunctionMap {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).obj
      ((schemeGlobalDerivedHom X).obj (op P.obj, (a.obj K).obj)) ⟶
      (schemeGlobalDerivedHom Y).obj (op ((schemeDerivedDirectImage f).obj P.obj), K.obj) :=
  schemeGlobalHomDirectImageMap f P.obj (a.obj K).obj ≫
    (schemeGlobalDerivedHom Y).map ((𝟙 _).op, (adj.counit.app K).hom)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The counit-induced global Hom adjunction is invertible, naturally in P and K.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof:
1. The qcqs right adjoint supplies the counit (sheafy trace). The evaluation-mate
comparison followed by internal Hom of this counit is invertible after DQ_Y, by
lem-pc-qcqs-sheaf-rhom-adjunction.
2. Apply derived global sections and the canonical Leray comparison. This is the
map above, by def-pc-global-derived-rhom and derived direct-image composition.
3. By lem-pc-dq-coherator-adjunction, H^i(Y,E) = Hom(O_Y[-i],DQ_Y(E)), since O_Y[-i]
is quasi-coherent. Thus the comparison is a quasi-isomorphism on global sections.
4. Naturality of the comparisons and the counit supplies naturality in both entries. -/
theorem schemeGlobalHomAdjunctionMap_isIso {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a) :
    (∀ (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y),
      IsIso (schemeGlobalHomAdjunctionMap f a adj P K)) ∧
    (∀ (P P' : schemeDerivedQCohCategory X) (K K' : schemeDerivedQCohCategory Y)
        (s : P' ⟶ P) (t : K ⟶ K'),
      (schemeGlobalScalarRestriction f).map
        ((schemeGlobalDerivedHom X).map (s.hom.op, (a.map t).hom)) ≫
          schemeGlobalHomAdjunctionMap f a adj P' K' =
        schemeGlobalHomAdjunctionMap f a adj P K ≫
          (schemeGlobalDerivedHom Y).map
            (((schemeDerivedDirectImage f).map s.hom).op, t.hom)) := by
  let Hx := derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
  let Hy := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let R := schemeDerivedDirectImage f
  let G := schemeDerivedGlobalSections Y
  let c := Classical.choose (exists_schemeHomDirectImageComparison f)
  let bx (L : schemeDerivedCategory X) := Adjunction.mkOfHomEquiv
    (@tensorAdjunctionCore (schemeDerivedCategory X) inferInstance
      (schemeDerivedTensorMonoidal X) Hx (schemeDerivedTensorHomEquiv X)
      (schemeHomTensorHom_naturality X) L)
  let by' (L : schemeDerivedCategory Y) := Adjunction.mkOfHomEquiv
    (@tensorAdjunctionCore (schemeDerivedCategory Y) inferInstance
      (schemeDerivedTensorMonoidal Y) Hy (schemeDerivedTensorHomEquiv Y)
      (schemeHomTensorHom_naturality Y) L)
  obtain ⟨DQ, ⟨coh⟩⟩ := exists_dqCoheratorAdjunction Y
  have hc : ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
      (α : A ⟶ R.obj (Hx.obj (op L, M))),
      ((by' (R.obj L)).homEquiv A (R.obj M)).symm (α ≫ c.app (op L, M)) =
        (schemeHomPullbackAdjunction f).homEquiv _ M
          ((mixedHomTensorPullbackIso f).hom.app (A, R.obj L) ≫
            (𝟙 _ ⊗ₘ (schemeHomPullbackAdjunction f).counit.app L) ≫
            ((bx L).homEquiv _ M).symm
              (((schemeHomPullbackAdjunction f).homEquiv A
                (Hx.obj (op L, M))).symm α)) := by
    intro L M A α
    simp only [bx, by', Adjunction.mkOfHomEquiv_homEquiv,
      tensorAdjunctionCore, Equiv.symm_symm, Hx, R, c, Functor.prod_obj, tensorRight,
      Functor.flip_obj_obj, curriedTensor_obj_obj, tensor]
    exact (Classical.choose_spec (exists_schemeHomDirectImageComparison f)) L M A α
  have h := qcqsSheafRHomAdjunction X Y f
    (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst a adj DQ coh
    (schemeHomPullbackAdjunction f) bx by' (mixedHomTensorPullbackIso f) c hc
  constructor
  · intro P K
    have hPK := h.2 P K
    change IsIso (DQ.map (c.app (op P.obj, (a.obj K).obj) ≫
      Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
        (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom))) at hPK
    have := dqCoherator_isIso_derivedGlobalSections Y DQ coh
      (c.app (op P.obj, (a.obj K).obj) ≫
        Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
          (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom))
    dsimp only [schemeGlobalHomAdjunctionMap, schemeGlobalHomDirectImageMap,
      schemeGlobalDerivedHom, Functor.comp_map]
    simp only [Category.assoc]
    change IsIso ((mixedGlobalSectionsDirectImageIso f).inv.app _ ≫
      G.map (c.app (op P.obj, (a.obj K).obj)) ≫
        G.map (Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
          (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom)))
    rw [← CategoryTheory.Functor.map_comp]
    infer_instance
  · intro P P' K K' s t
    have hn := h.1 P P' K K' s t
    have hn' : R.map
        (Hx.map (X := (op P.obj, (a.obj K).obj))
          (Y := (op P'.obj, (a.obj K').obj)) (s.hom.op, (a.map t).hom)) ≫
        (c.app (op P'.obj, (a.obj K').obj) ≫
          Hy.map (X := (op (R.obj P'.obj), R.obj (a.obj K').obj))
            (Y := (op (R.obj P'.obj), K'.obj)) ((𝟙 _).op, (adj.counit.app K').hom)) =
      (c.app (op P.obj, (a.obj K).obj) ≫
        Hy.map (X := (op (R.obj P.obj), R.obj (a.obj K).obj))
          (Y := (op (R.obj P.obj), K.obj)) ((𝟙 _).op, (adj.counit.app K).hom)) ≫
        Hy.map (X := (op (R.obj P.obj), K.obj))
          (Y := (op (R.obj P'.obj), K'.obj)) ((R.map s.hom).op, t.hom) := hn
    have hl := lerayNaturality R G (schemeDerivedGlobalSections X)
      (schemeGlobalScalarRestriction f) (mixedGlobalSectionsDirectImageIso f)
      _ _ _ _ hn'
    simpa only [schemeGlobalHomAdjunctionMap, schemeGlobalHomDirectImageMap,
      schemeGlobalDerivedHom, Functor.comp_map, CategoryTheory.Functor.map_comp,
      Category.assoc] using hl


/-- The canonical global Hom adjunction iso.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomAdjunctionIso {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).obj
      ((schemeGlobalDerivedHom X).obj (op P.obj, (a.obj K).obj)) ≅
      (schemeGlobalDerivedHom Y).obj (op ((schemeDerivedDirectImage f).obj P.obj), K.obj) :=
  haveI := (schemeGlobalHomAdjunctionMap_isIso f a adj).1 P K
  asIso (schemeGlobalHomAdjunctionMap f a adj P K)

end AlgebraicGeometry
