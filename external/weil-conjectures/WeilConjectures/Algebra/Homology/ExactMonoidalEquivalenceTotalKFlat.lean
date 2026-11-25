/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.CountableTensorStructures
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact symmetric monoidal equivalences and signed total K-flatness

Source: Stacks Project, Tag 06YP, `lemma-K-flat-quasi-isomorphism`, and the
explicit exact-equivalence and signed-total extension in the blueprint
(auxiliary; not a blueprint node).

The comparison is specified by its action on every summand, together with
naturality, associativity, unit, and Koszul symmetry equations. The inverse
comparison is specified relative to the termwise equivalence's unit and counit.
The final clauses compare the acyclic and arbitrary-endpoint quasi-isomorphism
K-flat tests, without requiring exactness of countable coproducts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe uM vM uA vA

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ZeroObject

namespace CategoryTheory.Equivalence

variable {M : Type uM} {A : Type uA} [Category.{vM} M] [Category.{vA} A]
  [Abelian M] [Abelian A] [MonoidalCategory M] [MonoidalCategory A]
  [MonoidalPreadditive M] [MonoidalPreadditive A]
  [SymmetricCategory M] [SymmetricCategory A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A]

private noncomputable def tensorComparison (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj Q :=
  asIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

private noncomputable def unitComparison (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    (F.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex M ℤ)) ≅
      𝟙_ (CochainComplex A ℤ) :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ M) ≪≫
    (HomologicalComplex.single A (.up ℤ) 0).mapIso (Functor.Monoidal.εIso F).symm

omit [SymmetricCategory M] [SymmetricCategory A] in
@[reassoc]
private theorem tensorComparison_ι (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q : CochainComplex M ℤ) (p q n : ℤ) (h : p + q = n) :
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (tensorComparison F P Q).hom.f n =
      Functor.OplaxMonoidal.δ F (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P Q p q n h

omit [MonoidalCategory M] [MonoidalCategory A] [MonoidalPreadditive M]
  [MonoidalPreadditive A] [SymmetricCategory M] [SymmetricCategory A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A] in
private theorem acyclic_map_iff (F : M ⥤ A) [F.Additive] [F.IsEquivalence]
    (P : CochainComplex M ℤ) :
    P.Acyclic ↔ ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  constructor
  · intro h n
    exact (P.sc n).exact_map_iff_of_faithful F |>.2 (h n)
  · intro h n
    exact (P.sc n).exact_map_iff_of_faithful F |>.1 (h n)

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem tensorComparison_naturality (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q P' Q' : CochainComplex M ℤ) (a : P ⟶ P') (b : Q ⟶ Q') :
    (F.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ b) ≫
        (tensorComparison F P' Q').hom =
      (tensorComparison F P Q).hom ≫
        ((F.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
          (F.mapHomologicalComplex (.up ℤ)).map b) := by
  exact HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) a b

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem unitComparison_zero (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).hom ≫
        (Functor.Monoidal.εIso F).inv =
      (unitComparison F).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom := by
  simp [unitComparison, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_associativity (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P Q R : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (α_ P Q R).hom ≫
        (tensorComparison F P (Q ⊗ R)).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).obj P ◁ (tensorComparison F Q R).hom =
      (tensorComparison F (P ⊗ Q) R).hom ≫
        (tensorComparison F P Q).hom ▷ (F.mapHomologicalComplex (.up ℤ)).obj R ≫
        (α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)
          ((F.mapHomologicalComplex (.up ℤ)).obj R)).hom := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro s r hsr
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map (tensorRight (R.X r) ⋙ F)
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change F.map (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫ _ =
    F.map (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫ _
  have ha : (HomologicalComplex.ιTensorObj P Q p q s hpq ▷ R.X r) ≫
      HomologicalComplex.ιTensorObj (P ⊗ Q) R s r n hsr ≫ (α_ P Q R).hom.f n =
      (α_ (P.X p) (Q.X q) (R.X r)).hom ≫
        (P.X p ◁ HomologicalComplex.ιTensorObj Q R q r (q + r) rfl) ≫
        HomologicalComplex.ιTensorObj P (Q ⊗ R) p (q + r) n
          (by change p + q = s at hpq; change s + r = n at hsr; omega) := by
    rw [← Category.assoc, ← CochainComplex.Monoidal.ι₁₂_eq P Q R p q r s n hpq hsr,
      CochainComplex.Monoidal.ι₁₂_associator_hom,
      CochainComplex.Monoidal.ι₂₃_eq P Q R p q r (q + r) n rfl]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ha,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    tensorComparison_ι_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f,
    ← whiskerLeft_comp_assoc, tensorComparison_ι]
  erw [tensorComparison_ι_assoc, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
    CochainComplex.Monoidal.ι_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    tensorComparison_ι]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  erw [← Category.assoc _ _ ((α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R)).hom.f n),
    ← CochainComplex.Monoidal.ι₁₂_eq
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R) p q r s n hpq hsr,
    CochainComplex.Monoidal.ι₁₂_associator_hom,
    CochainComplex.Monoidal.ι₂₃_eq
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj R) p q r (q + r) n rfl]
  · rw [← Functor.OplaxMonoidal.associativity_assoc]
    rfl

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem unitComparison_inv_zero (F : M ⥤ A) [F.Additive] [F.Monoidal] :
    F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ≫
        (unitComparison F).hom.f 0 =
      Functor.OplaxMonoidal.η F ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv := by
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom).mp
  simp only [Category.assoc, ← unitComparison_zero, ← F.map_comp_assoc,
    Iso.inv_hom_id, F.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rfl

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_leftUnitor (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom =
      (tensorComparison F (𝟙_ (CochainComplex M ℤ)) P).hom ≫
        (unitComparison F).hom ▷ (F.mapHomologicalComplex (.up ℤ)).obj P ≫
        (λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (λ_ P).inv)).mp
  ext n
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Functor.mapHomologicalComplex_map_f]
  change 𝟙 _ = F.map ((HomologicalComplex.leftUnitor P).inv.f n) ≫ _
  rw [show (HomologicalComplex.leftUnitor P).inv.f n =
      (λ_ (P.X n)).inv ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ▷ P.X n ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex M ℤ)) P 0 n n
          (zero_add n) from HomologicalComplex.leftUnitor'_inv P n]
  simp only [Functor.map_comp, Category.assoc]
  rw [tensorComparison_ι_assoc, CochainComplex.Monoidal.ι_whiskerRight_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  erw [← comp_whiskerRight_assoc, unitComparison_inv_zero]
  simp only [comp_whiskerRight, Category.assoc]
  have hi :
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ▷ F.obj (P.X n) ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex A ℤ))
          ((F.mapHomologicalComplex (.up ℤ)).obj P) 0 n n (zero_add n) =
      (λ_ (F.obj (P.X n))).hom ≫
        (λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n := by
    change _ = (λ_ (F.obj (P.X n))).hom ≫
      (HomologicalComplex.leftUnitor ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n
    rw [show (HomologicalComplex.leftUnitor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n = _ from
      HomologicalComplex.leftUnitor'_inv ((F.mapHomologicalComplex (.up ℤ)).obj P) n]
    erw [Iso.hom_inv_id_assoc]
    rfl
  rw [← Category.assoc _ _ ((λ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom.f n), hi]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  change 𝟙 _ = F.map (λ_ (P.X n)).inv ≫
    Functor.OplaxMonoidal.δ F (𝟙_ M) (P.X n) ≫
      Functor.OplaxMonoidal.η F ▷ F.obj (P.X n) ≫ (λ_ (F.obj (P.X n))).hom ≫ 𝟙 _
  rw [Category.comp_id, Functor.OplaxMonoidal.left_unitality_hom,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]

omit [SymmetricCategory M] [SymmetricCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_rightUnitor (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] (P : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom =
      (tensorComparison F P (𝟙_ (CochainComplex M ℤ))).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).obj P ◁ (unitComparison F).hom ≫
        (ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).inv)).mp
  ext n
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Functor.mapHomologicalComplex_map_f]
  change 𝟙 _ = F.map ((HomologicalComplex.rightUnitor P).inv.f n) ≫ _
  rw [show (HomologicalComplex.rightUnitor P).inv.f n =
      (ρ_ (P.X n)).inv ≫
        P.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).inv ≫
        HomologicalComplex.ιTensorObj P (𝟙_ (CochainComplex M ℤ)) n 0 n
          (add_zero n) from HomologicalComplex.rightUnitor'_inv P n]
  simp only [Functor.map_comp, Category.assoc]
  rw [tensorComparison_ι_assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  erw [← whiskerLeft_comp_assoc, unitComparison_inv_zero]
  simp only [whiskerLeft_comp, Category.assoc]
  have hi :
      F.obj (P.X n) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).inv ≫
        HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
          (𝟙_ (CochainComplex A ℤ)) n 0 n (add_zero n) =
      (ρ_ (F.obj (P.X n))).hom ≫
        (ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n := by
    change _ = (ρ_ (F.obj (P.X n))).hom ≫
      (HomologicalComplex.rightUnitor ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n
    rw [show (HomologicalComplex.rightUnitor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).inv.f n = _ from
      HomologicalComplex.rightUnitor'_inv ((F.mapHomologicalComplex (.up ℤ)).obj P) n]
    erw [Iso.hom_inv_id_assoc]
    rfl
  rw [← Category.assoc _ _ ((ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom.f n), hi]
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  change 𝟙 _ = F.map (ρ_ (P.X n)).inv ≫
    Functor.OplaxMonoidal.δ F (P.X n) (𝟙_ M) ≫
      F.obj (P.X n) ◁ Functor.OplaxMonoidal.η F ≫ (ρ_ (F.obj (P.X n))).hom ≫ 𝟙 _
  rw [Category.comp_id, Functor.OplaxMonoidal.right_unitality_hom,
    ← F.map_comp, Iso.inv_hom_id, F.map_id]


set_option backward.isDefEq.respectTransparency false in
private theorem tensorComparison_braiding (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence]
    (hβ : ∀ X Y : M,
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
        Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (P Q : CochainComplex M ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.Monoidal.braiding P Q).hom ≫
        (tensorComparison F Q P).hom =
      (tensorComparison F P Q).hom ≫
        (CochainComplex.Monoidal.braiding
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ← Functor.map_comp_assoc]
  rw [CochainComplex.Monoidal.ι_braiding_hom, Functor.map_zsmul,
    Functor.map_comp, Preadditive.zsmul_comp, Category.assoc, tensorComparison_ι]
  rw [tensorComparison_ι_assoc, CochainComplex.Monoidal.ι_braiding_hom,
    Preadditive.comp_zsmul, ← Category.assoc, hβ]
  simp only [Category.assoc]
  rfl

private theorem acyclic_of_iso {C : Type*} [Category C] [Abelian C]
    {P Q : CochainComplex C ℤ} (e : P ≅ Q) (h : P.Acyclic) : Q.Acyclic :=
  fun n ↦ (h n).of_iso e

omit [SymmetricCategory M] [SymmetricCategory A] in
private theorem acyclic_tensor_map_iff (E : M ≌ A)
    [E.functor.Additive] [E.inverse.Additive] [E.functor.Monoidal]
    (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (∀ N : CochainComplex A ℤ, N.Acyclic →
        ((E.functor.mapHomologicalComplex (.up ℤ)).obj P ⊗ N).Acyclic) := by
  let F := E.functor.mapHomologicalComplex (.up ℤ)
  let G := E.inverse.mapHomologicalComplex (.up ℤ)
  constructor
  · intro h N hN
    have hG := (acyclic_map_iff E.inverse N).mp hN
    have hF := (acyclic_map_iff E.functor (P ⊗ G.obj N)).mp (h _ hG)
    exact acyclic_of_iso (tensorComparison E.functor P (G.obj N) ≪≫
      (tensorLeft (F.obj P)).mapIso ((E.mapHomologicalComplex (.up ℤ)).counitIso.app N)) hF
  · intro h N hN
    have hF := h (F.obj N) ((acyclic_map_iff E.functor N).mp hN)
    exact (acyclic_map_iff E.functor (P ⊗ N)).mpr
      (acyclic_of_iso (tensorComparison E.functor P N).symm hF)

private theorem acyclic_tensor_swap (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (∀ N : CochainComplex M ℤ, N.Acyclic → (N ⊗ P).Acyclic) := by
  constructor <;> intro h N hN
  · exact acyclic_of_iso (CochainComplex.Monoidal.braiding P N) (h N hN)
  · exact acyclic_of_iso (CochainComplex.Monoidal.braiding N P) (h N hN)

private theorem acyclic_tensor_iff_kFlat (P : CochainComplex M ℤ) :
    (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
      (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P := by
  constructor
  · intro h
    have hleft : ∀ {X Y : CochainComplex M ℤ} (s : X ⟶ Y), QuasiIso s →
        QuasiIso (HomologicalComplex.tensorHom (𝟙 P) s) := by
      intro X Y s hs
      let := HasDerivedCategory.standard M
      obtain ⟨φ, _⟩ := CochainComplex.exists_totalTensorConeComparison M
      apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).mpr
      exact acyclic_of_iso (φ P X Y s)
        (h _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic s).mp hs))
    refine ⟨fun _ _ s hs ↦ hleft s hs, ?_⟩
    intro X Y s hs
    change QuasiIso (HomologicalComplex.tensorHom s (𝟙 P))
    have := hleft s hs
    have he : HomologicalComplex.tensorHom s (𝟙 P) =
        (CochainComplex.Monoidal.braiding P X).inv ≫
          HomologicalComplex.tensorHom (𝟙 P) s ≫
          (CochainComplex.Monoidal.braiding P Y).hom := by
      change s ▷ P = (CochainComplex.Monoidal.braiding P X).inv ≫ P ◁ s ≫
        (CochainComplex.Monoidal.braiding P Y).hom
      rw [CochainComplex.Monoidal.braiding_naturality_right,
        Iso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  · intro h N hN
    let Z : CochainComplex M ℤ := 0
    have hZ : Z.Acyclic := HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
    have hs : QuasiIso (0 : Z ⟶ N) := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt _ n (hZ n)).mpr (hN n)
    have ht : QuasiIso (HomologicalComplex.tensorHom (𝟙 P) (0 : Z ⟶ N)) := h.1 _ hs
    have hz : (P ⊗ Z).Acyclic := by
      have : (tensorLeft P).Additive :=
        inferInstanceAs (((curriedTensor M).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)).obj P).Additive
      exact HomologicalComplex.acyclic_of_isZero _
        ((tensorLeft P).map_isZero (isZero_zero _))
    intro n
    have : QuasiIsoAt
        (HomologicalComplex.tensorHom (𝟙 P) (0 : Z ⟶ N)) n :=
      (quasiIso_iff _).mp ht n
    exact (quasiIsoAt_iff_exactAt _ n (hz n)).mp this

omit [SymmetricCategory M] [SymmetricCategory A] [Abelian M] [Abelian A]
  [MonoidalPreadditive M] [MonoidalPreadditive A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A] in
private theorem flat_map (E : M ≌ A) [E.functor.Monoidal]
    (X : M) (hX : ObjectProperty.flat X) : ObjectProperty.flat (E.functor.obj X) := by
  have : PreservesFiniteLimits (tensorLeft X) := hX.1.1
  have : PreservesFiniteColimits (tensorLeft X) := hX.1.2
  have : PreservesFiniteLimits (tensorRight X) := hX.2.1
  have : PreservesFiniteColimits (tensorRight X) := hX.2.2
  let eL : E.inverse ⋙ tensorLeft X ⋙ E.functor ≅ tensorLeft (E.functor.obj X) :=
    Functor.isoWhiskerLeft E.inverse (Functor.Monoidal.commTensorLeft E.functor X).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso (tensorLeft (E.functor.obj X)) ≪≫ Functor.leftUnitor _
  let eR : E.inverse ⋙ tensorRight X ⋙ E.functor ≅ tensorRight (E.functor.obj X) :=
    Functor.isoWhiskerLeft E.inverse (Functor.Monoidal.commTensorRight E.functor X).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso (tensorRight (E.functor.obj X)) ≪≫ Functor.leftUnitor _
  have : PreservesFiniteLimits (E.inverse ⋙ tensorLeft X ⋙ E.functor) :=
    by
      have := comp_preservesFiniteLimits (tensorLeft X) E.functor
      exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (E.inverse ⋙ tensorLeft X ⋙ E.functor) := by
    have := comp_preservesFiniteColimits (tensorLeft X) E.functor
    exact comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (E.inverse ⋙ tensorRight X ⋙ E.functor) := by
    have := comp_preservesFiniteLimits (tensorRight X) E.functor
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (E.inverse ⋙ tensorRight X ⋙ E.functor) := by
    have := comp_preservesFiniteColimits (tensorRight X) E.functor
    exact comp_preservesFiniteColimits _ _
  exact ⟨⟨preservesFiniteLimits_of_natIso eL, preservesFiniteColimits_of_natIso eL⟩,
    ⟨preservesFiniteLimits_of_natIso eR, preservesFiniteColimits_of_natIso eR⟩⟩

omit [SymmetricCategory M] [SymmetricCategory A] in
@[instance_reducible]
private noncomputable def complexOplax (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] : (F.mapHomologicalComplex (.up ℤ)).OplaxMonoidal where
  η := (unitComparison F).hom
  δ P Q := (tensorComparison F P Q).hom
  δ_natural_left f Q := by
    simpa using (tensorComparison_naturality F _ Q _ Q f (𝟙 Q)).symm
  δ_natural_right P g := by
    simpa using (tensorComparison_naturality F P _ P _ (𝟙 P) g).symm
  oplax_associativity P Q R := (tensorComparison_associativity F P Q R).symm
  oplax_left_unitality P := by
    apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    rw [tensorComparison_leftUnitor]
    simp
  oplax_right_unitality P := by
    apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    rw [tensorComparison_rightUnitor]
    simp

omit [SymmetricCategory M] [SymmetricCategory A] in
@[instance_reducible]
private noncomputable def complexMonoidal (F : M ⥤ A) [F.Additive] [F.Monoidal]
    [F.IsEquivalence] : (F.mapHomologicalComplex (.up ℤ)).Monoidal := by
  letI := complexOplax F
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ))) :=
    inferInstanceAs (IsIso (unitComparison F).hom)
  have (P Q : CochainComplex M ℤ) :
      IsIso (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P Q) :=
    inferInstanceAs (IsIso (tensorComparison F P Q).hom)
  exact Functor.Monoidal.ofOplaxMonoidal _

private theorem inverse_braiding {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (E : C ≌ D) [E.functor.Monoidal] [E.inverse.Monoidal] [E.IsMonoidal]
    (hβ : ∀ X Y : C,
      E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X =
        Functor.OplaxMonoidal.δ E.functor X Y ≫
          (β_ (E.functor.obj X) (E.functor.obj Y)).hom)
    (X Y : D) :
    E.inverse.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.inverse Y X =
      Functor.OplaxMonoidal.δ E.inverse X Y ≫
        (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom := by
  have hc (U V : D) :
      E.functor.map (Functor.OplaxMonoidal.δ E.inverse U V) ≫
        Functor.OplaxMonoidal.δ E.functor (E.inverse.obj U) (E.inverse.obj V) ≫
        (E.counitIso.hom.app U ⊗ₘ E.counitIso.hom.app V) =
      E.counitIso.hom.app (U ⊗ V) := by
    apply (cancel_epi (E.functor.map (Functor.LaxMonoidal.μ E.inverse U V))).mp
    simp only [← E.functor.map_comp_assoc, Functor.Monoidal.μ_δ,
      E.functor.map_id, Category.id_comp]
    exact (E.functor_map_μ_inverse_comp_counitIso_hom_app_tensor U V).symm
  apply E.functor.map_injective
  apply (cancel_mono (Functor.OplaxMonoidal.δ E.functor
    (E.inverse.obj Y) (E.inverse.obj X) ≫
      (E.counitIso.hom.app Y ⊗ₘ E.counitIso.hom.app X))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  erw [E.counitIso.hom.naturality]
  rw [← Category.assoc (E.functor.map (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom),
    hβ, Category.assoc, ← BraidedCategory.braiding_naturality]
  rw [reassoc_of% (hc X Y)]
  rfl

/-- An additive exact symmetric strong monoidal equivalence commutes coherently
with signed total tensor, reflects flatness, and identifies both K-flat tests.
Source: Stacks Project, Tag 06YP and the explicit abstract extension
(auxiliary; not a blueprint node).

Proof:
1. `lem-weil-pbc-exact-functor-complex-cohomology` identifies the homology of
   termwise images with images of homology. Faithfulness reflects zero objects
   and the quasi-inverse reflects invertibility. This gives both directions of
   the acyclicity and quasi-isomorphism clauses for both functors.
2. `lem-galois-equivalence-preserves-limits` supplies preservation of the
   countable coproducts. `lem-sfb-monoidal-equivalence-inverse-structure` equips
   the inverse with its canonical strong monoidal structure, whose four
   equations are relative to the given equivalence's unit and counit.
3. On the degree-n coproduct, define tau by the inverse tensorator followed by
   each target coprojection. Its inverse uses the forward tensorator followed
   by the image of the source coprojection. Coproduct uniqueness proves that
   these maps are inverse (`def-weil-pbc-category-colimit`).
4. On a (p,q) summand, the two chain-map composites are the sum of the image
   of d_P tensor identity and (-1)^p times identity tensor the image of d_Q.
   Additivity carries the integer sign through the functor, including negative
   degrees. Tensorator naturality proves naturality in both complex arguments.
5. The ordinary total associator reindexes triple summands and is a chain
   map: both differentials have coefficients 1, (-1)^p, (-1)^(p+q). Tensor
   preserves the requisite countable coproducts. Pentagon and triangle reduce
   to those of the coefficient category. The unit is the tensor unit in degree
   zero; the unitors use the coefficient unitors on the (0,n) and (n,0) terms.
6. Test the associativity comparison on triple coprojections. It becomes the
   inverse-tensorator associativity axiom of `def-sfb-strong-monoidal-functor`.
   The unit comparison is the inverse unit structure map in degree zero and
   the unique zero-object maps elsewhere. Its two unitor equations become
   exactly the inverse forms of the coefficient unit axioms.
7. The Koszul swap is (-1)^(pq) times beta on a (p,q) summand. Compatibility
   with d_P uses pq+q=(p+1)q; compatibility with d_Q uses equality modulo two
   of pq and p+p(q+1). Its inverse uses beta in the opposite order; the hexagon
   uses p(q+r)=pq+pr. The symmetry equation for tau reduces to the given
   symmetric-functor equation, since the functor preserves integer multiples.
8. Regard tau and the unit comparison as the strong monoidal structure on
   the termwise forward functor. Apply the canonical inverse-structure theorem
   from step 2 directly to the equivalence of complexes. Its axioms give inverse
   naturality, associativity, both unitors, and the four unit/counit equations.
   Its symmetry follows by applying the faithful forward functor, using the
   counit tensor equation, counit naturality, and forward symmetry.
9. Tensor with F(X) is naturally isomorphic to the composite of the inverse
   functor, tensor with X, and the forward functor, by the tensorator and the
   counit. Exactness is preserved by composition and natural isomorphism.
   Apply the same argument to the inverse and use the unit to get reflection.
10. Test an image complex against an acyclic N. Its inverse image is acyclic
    by step 1. Tau followed by tensoring the counit identifies its tensor with
    the forward image of the tested tensor. Step 1 preserves and reflects
    acyclicity, giving both directions; the Koszul swap handles either order.
11. If P passes the acyclic test and u is any quasi-isomorphism, its cone is
    acyclic (`lem-pur-quasi-iso-cone-acyclic`). By
    `lem-sfb-additive-total-tensor-cone-comparison`, tensoring that cone is
    chain-isomorphic to the cone of tensoring u. Transfer acyclicity across
    this isomorphism, then use the cone criterion again. Koszul
    symmetry gives the other tensor order. Endpoints of u are unrestricted.
12. Conversely apply the quasi-isomorphism test to zero into any acyclic
    complex. Additivity identifies its tensored source with a zero object,
    so its target is acyclic. Combine this equivalence of tests in each
    category with step 10 to get preservation and reflection of both tests
    by both termwise functors. -/
theorem exactMonoidal_totalTensor_kFlat (E : M ≌ A)
    [E.functor.Additive] [E.inverse.Additive] [E.functor.Monoidal]
    (hβ : ∀ X Y : M,
      E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X =
        Functor.OplaxMonoidal.δ E.functor X Y ≫ (β_ (E.functor.obj X) (E.functor.obj Y)).hom) :
    ∃ (τ : ∀ P Q : CochainComplex M ℤ,
        (E.functor.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
          (E.functor.mapHomologicalComplex (.up ℤ)).obj P ⊗
            (E.functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (j : (E.functor.mapHomologicalComplex (.up ℤ)).obj
          (𝟙_ (CochainComplex M ℤ)) ≅ 𝟙_ (CochainComplex A ℤ))
      (υ : ∀ P Q : CochainComplex A ℤ,
        (E.inverse.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
          (E.inverse.mapHomologicalComplex (.up ℤ)).obj P ⊗
            (E.inverse.mapHomologicalComplex (.up ℤ)).obj Q)
      (k : (E.inverse.mapHomologicalComplex (.up ℤ)).obj
          (𝟙_ (CochainComplex A ℤ)) ≅ 𝟙_ (CochainComplex M ℤ)),
    (∀ (P Q : CochainComplex M ℤ) (p q n : ℤ) (h : p + q = n),
      E.functor.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (τ P Q).hom.f n =
        Functor.OplaxMonoidal.δ E.functor (P.X p) (Q.X q) ≫
          HomologicalComplex.ιTensorObj
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ∧
    (E.functor.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ M)).hom ≫
        (Functor.Monoidal.εIso E.functor).inv =
      j.hom.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).hom) ∧
    (∀ (P Q P' Q' : CochainComplex M ℤ) (a : P ⟶ P') (b : Q ⟶ Q'),
      (E.functor.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ b) ≫ (τ P' Q').hom =
        (τ P Q).hom ≫ ((E.functor.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
          (E.functor.mapHomologicalComplex (.up ℤ)).map b)) ∧
    (∀ P Q R : CochainComplex M ℤ,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (α_ P Q R).hom ≫ (τ P (Q ⊗ R)).hom ≫
          (E.functor.mapHomologicalComplex (.up ℤ)).obj P ◁ (τ Q R).hom =
        (τ (P ⊗ Q) R).hom ≫ (τ P Q).hom ▷ (E.functor.mapHomologicalComplex (.up ℤ)).obj R ≫
          (α_ ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q) ((E.functor.mapHomologicalComplex
          (.up ℤ)).obj R)).hom) ∧
    (∀ P : CochainComplex M ℤ,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom =
        (τ (𝟙_ (CochainComplex M ℤ)) P).hom ≫ j.hom ▷ (E.functor.mapHomologicalComplex (.up ℤ)).obj
          P ≫
          (λ_ ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)).hom) ∧
    (∀ P : CochainComplex M ℤ,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom =
        (τ P (𝟙_ (CochainComplex M ℤ))).hom ≫ (E.functor.mapHomologicalComplex (.up ℤ)).obj P ◁
          j.hom ≫
          (ρ_ ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)).hom) ∧
    (∀ P Q : CochainComplex M ℤ,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (CochainComplex.Monoidal.braiding P Q).hom ≫ (τ
          Q P).hom =
        (τ P Q).hom ≫ (CochainComplex.Monoidal.braiding
          ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) ((E.functor.mapHomologicalComplex (.up
          ℤ)).obj Q)).hom) ∧
    (∀ (P Q P' Q' : CochainComplex A ℤ) (a : P ⟶ P') (b : Q ⟶ Q'),
      (E.inverse.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ b) ≫ (υ P' Q').hom =
        (υ P Q).hom ≫ ((E.inverse.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
          (E.inverse.mapHomologicalComplex (.up ℤ)).map b)) ∧
    (∀ P Q R : CochainComplex A ℤ,
      (E.inverse.mapHomologicalComplex (.up ℤ)).map (α_ P Q R).hom ≫ (υ P (Q ⊗ R)).hom ≫
          (E.inverse.mapHomologicalComplex (.up ℤ)).obj P ◁ (υ Q R).hom =
        (υ (P ⊗ Q) R).hom ≫ (υ P Q).hom ▷ (E.inverse.mapHomologicalComplex (.up ℤ)).obj R ≫
          (α_ ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.inverse.mapHomologicalComplex (.up ℤ)).obj Q) ((E.inverse.mapHomologicalComplex
          (.up ℤ)).obj R)).hom) ∧
    (∀ P : CochainComplex A ℤ,
      (E.inverse.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom =
        (υ (𝟙_ (CochainComplex A ℤ)) P).hom ≫ k.hom ▷ (E.inverse.mapHomologicalComplex (.up ℤ)).obj
          P ≫
          (λ_ ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)).hom) ∧
    (∀ P : CochainComplex A ℤ,
      (E.inverse.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom =
        (υ P (𝟙_ (CochainComplex A ℤ))).hom ≫ (E.inverse.mapHomologicalComplex (.up ℤ)).obj P ◁
          k.hom ≫
          (ρ_ ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)).hom) ∧
    (∀ P Q : CochainComplex A ℤ,
      (E.inverse.mapHomologicalComplex (.up ℤ)).map (CochainComplex.Monoidal.braiding P Q).hom ≫ (υ
          Q P).hom =
        (υ P Q).hom ≫ (CochainComplex.Monoidal.braiding
          ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P) ((E.inverse.mapHomologicalComplex (.up
          ℤ)).obj Q)).hom) ∧
    (∀ P Q : CochainComplex M ℤ,
      (E.mapHomologicalComplex (.up ℤ)).unitIso.hom.app (P ⊗ Q) ≫
          (E.inverse.mapHomologicalComplex (.up ℤ)).map (τ P Q).hom ≫
          (υ ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj Q)).hom =
        (E.mapHomologicalComplex (.up ℤ)).unitIso.hom.app P ⊗ₘ
          (E.mapHomologicalComplex (.up ℤ)).unitIso.hom.app Q) ∧
    (∀ P Q : CochainComplex A ℤ,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (υ P Q).hom ≫
          (τ ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.inverse.mapHomologicalComplex (.up ℤ)).obj Q)).hom ≫
          ((E.mapHomologicalComplex (.up ℤ)).counitIso.hom.app P ⊗ₘ
            (E.mapHomologicalComplex (.up ℤ)).counitIso.hom.app Q) =
        (E.mapHomologicalComplex (.up ℤ)).counitIso.hom.app (P ⊗ Q)) ∧
    ((E.mapHomologicalComplex (.up ℤ)).unitIso.hom.app (𝟙_ (CochainComplex M ℤ)) ≫
        (E.inverse.mapHomologicalComplex (.up ℤ)).map j.hom ≫ k.hom =
      𝟙 (𝟙_ (CochainComplex M ℤ))) ∧
    ((E.functor.mapHomologicalComplex (.up ℤ)).map k.hom ≫ j.hom =
      (E.mapHomologicalComplex (.up ℤ)).counitIso.hom.app (𝟙_ (CochainComplex A ℤ))) ∧
    (∀ P : CochainComplex M ℤ,
      P.Acyclic ↔ ((E.functor.mapHomologicalComplex (.up ℤ)).obj P).Acyclic) ∧
    (∀ (P Q : CochainComplex M ℤ) (s : P ⟶ Q),
      QuasiIso s ↔ QuasiIso ((E.functor.mapHomologicalComplex (.up ℤ)).map s)) ∧
    (∀ X : M, ObjectProperty.flat X ↔ ObjectProperty.flat (E.functor.obj X)) ∧
    (∀ P : CochainComplex M ℤ,
      (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (∀ N : CochainComplex A ℤ,
          N.Acyclic → ((E.functor.mapHomologicalComplex (.up ℤ)).obj P ⊗ N).Acyclic)) ∧
    (∀ P : CochainComplex M ℤ,
      (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P ↔
        (HomologicalComplex.quasiIso A (.up ℤ)).kFlat
          ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ P : CochainComplex A ℤ,
      P.Acyclic ↔ ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P).Acyclic) ∧
    (∀ (P Q : CochainComplex A ℤ) (s : P ⟶ Q),
      QuasiIso s ↔ QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map s)) ∧
    (∀ X : A, ObjectProperty.flat X ↔ ObjectProperty.flat (E.inverse.obj X)) ∧
    (∀ P : CochainComplex A ℤ,
      (∀ N : CochainComplex A ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (∀ N : CochainComplex M ℤ,
          N.Acyclic → ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P ⊗ N).Acyclic)) ∧
    (∀ P : CochainComplex A ℤ,
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P ↔
        (HomologicalComplex.quasiIso M (.up ℤ)).kFlat
          ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ P : CochainComplex M ℤ,
      (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P) ∧
    (∀ P : CochainComplex M ℤ,
      (∀ N : CochainComplex M ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (∀ N : CochainComplex M ℤ, N.Acyclic → (N ⊗ P).Acyclic)) ∧
    (∀ P : CochainComplex A ℤ,
      (∀ N : CochainComplex A ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) ∧
    (∀ P : CochainComplex A ℤ,
      (∀ N : CochainComplex A ℤ, N.Acyclic → (P ⊗ N).Acyclic) ↔
        (∀ N : CochainComplex A ℤ, N.Acyclic → (N ⊗ P).Acyclic)) := by
  let := E.inverseMonoidal
  have : E.symm.functor.Additive := inferInstanceAs E.inverse.Additive
  have : E.symm.inverse.Additive := inferInstanceAs E.functor.Additive
  let EC := E.mapHomologicalComplex (.up ℤ)
  let : EC.functor.Monoidal := complexMonoidal E.functor
  let := EC.inverseMonoidal
  have hE : EC.IsMonoidal := by
    change EC.toAdjunction.IsMonoidal
    infer_instance
  let τ := tensorComparison E.functor
  let j := unitComparison E.functor
  let υ := fun P Q : CochainComplex A ℤ ↦
    (Functor.Monoidal.μIso EC.inverse P Q).symm
  let k := (Functor.Monoidal.εIso EC.inverse).symm
  have hbraid (P Q : CochainComplex M ℤ) :
      EC.functor.map (β_ P Q).hom ≫ Functor.OplaxMonoidal.δ EC.functor Q P =
        Functor.OplaxMonoidal.δ EC.functor P Q ≫
          (β_ (EC.functor.obj P) (EC.functor.obj Q)).hom :=
    tensorComparison_braiding E.functor hβ P Q
  have hflat (X : M) : ObjectProperty.flat X ↔ ObjectProperty.flat (E.functor.obj X) := by
    constructor
    · exact flat_map E X
    · intro h
      exact (ObjectProperty.flat (A := M)).prop_of_iso (E.unitIso.app X).symm
        (flat_map E.symm (E.functor.obj X) h)
  have hflat' (X : A) : ObjectProperty.flat X ↔ ObjectProperty.flat (E.inverse.obj X) := by
    constructor
    · exact flat_map E.symm X
    · intro h
      exact (ObjectProperty.flat (A := A)).prop_of_iso (E.counitIso.app X)
        (flat_map E (E.inverse.obj X) h)
  refine ⟨τ, j, υ, k, tensorComparison_ι E.functor, unitComparison_zero E.functor,
    tensorComparison_naturality E.functor, tensorComparison_associativity E.functor,
    tensorComparison_leftUnitor E.functor, tensorComparison_rightUnitor E.functor,
    tensorComparison_braiding E.functor hβ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    acyclic_map_iff E.functor, ?_, hflat, acyclic_tensor_map_iff E, ?_,
    acyclic_map_iff E.inverse, ?_, hflat', acyclic_tensor_map_iff E.symm, ?_,
    acyclic_tensor_iff_kFlat, acyclic_tensor_swap, acyclic_tensor_iff_kFlat,
    acyclic_tensor_swap⟩
  · intro P Q P' Q' a b
    exact (Functor.OplaxMonoidal.δ_natural EC.inverse a b).symm
  · intro P Q R
    exact (Functor.OplaxMonoidal.associativity EC.inverse P Q R).symm
  · intro P
    exact (Functor.OplaxMonoidal.left_unitality_hom EC.inverse P).symm
  · intro P
    exact (Functor.OplaxMonoidal.right_unitality_hom EC.inverse P).symm
  · intro P Q
    exact inverse_braiding EC hbraid P Q
  · intro P Q
    change EC.unitIso.hom.app (P ⊗ Q) ≫
      EC.inverse.map (Functor.OplaxMonoidal.δ EC.functor P Q) ≫
        Functor.OplaxMonoidal.δ EC.inverse _ _ = _
    rw [EC.unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]
    simp
    rfl
  · intro P Q
    change EC.functor.map (Functor.OplaxMonoidal.δ EC.inverse P Q) ≫
      Functor.OplaxMonoidal.δ EC.functor _ _ ≫ _ = _
    apply (cancel_epi (EC.functor.map (Functor.LaxMonoidal.μ EC.inverse P Q))).mp
    simp only [← EC.functor.map_comp_assoc, Functor.Monoidal.μ_δ,
      EC.functor.map_id, Category.id_comp]
    exact (EC.functor_map_μ_inverse_comp_counitIso_hom_app_tensor P Q).symm
  · change EC.unitIso.hom.app _ ≫ EC.inverse.map
      (Functor.OplaxMonoidal.η EC.functor) ≫ Functor.OplaxMonoidal.η EC.inverse = _
    rw [EC.unitIso_hom_app_comp_inverse_map_η_functor_assoc]
    simp
  · change EC.functor.map (Functor.OplaxMonoidal.η EC.inverse) ≫
      Functor.OplaxMonoidal.η EC.functor = _
    apply (cancel_epi (EC.functor.map (Functor.LaxMonoidal.ε EC.inverse))).mp
    simp only [← EC.functor.map_comp_assoc, Functor.Monoidal.ε_η,
      EC.functor.map_id, Category.id_comp]
    exact (EC.functor_map_ε_inverse_comp_counitIso_hom_app).symm
  · intro P Q s
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology s E.functor).symm
  · intro P
    exact (acyclic_tensor_iff_kFlat P).symm.trans
      ((acyclic_tensor_map_iff E P).trans
        (acyclic_tensor_iff_kFlat ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)))
  · intro P Q s
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology s E.inverse).symm
  · intro P
    exact (acyclic_tensor_iff_kFlat P).symm.trans
      ((acyclic_tensor_map_iff E.symm P).trans
        (acyclic_tensor_iff_kFlat ((E.inverse.mapHomologicalComplex (.up ℤ)).obj P)))

end CategoryTheory.Equivalence
