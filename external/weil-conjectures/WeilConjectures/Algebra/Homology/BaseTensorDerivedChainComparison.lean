/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.BaseTensorCoefficientNaturalMap
import WeilConjectures.Algebra.Homology.ScalarExtensionDerivedRestriction

/-! # Comparison in the derived category, before homology -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- Derived coefficient chain comparison.
Source: Stacks Project, Tag 065Y, construction of equation-comparison-map
(Tag 065Z); Tag 06Y6; perfect.tex equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-tensor-derived-chain-comparison).

Proof: resolve an A-complex by an A-K-flat complex U and its restriction by an
R-K-flat complex V. The map V to Res(U) induces on pure tensors the displayed
coefficient map into Res(D tensor_A U). Invert the resolution counits and the
quasi-isomorphism U to P. Comparison maps of resolutions commute with this map
on pure tensors, and tensor induction proves the commuting squares. Applying
the same argument to roofs proves naturality and independence of refinements.
The augmentation squares and counit naturality give the displayed derived
equation at P, without assuming the counit at P is invertible. Finally use the
unique counit-compatible isomorphisms of left derived functors to transport the
construction to the supplied universal pairs F and L. -/
theorem exists_baseTensorDerivedChainComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (δ : DerivedCategory.Qh ⋙ F ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    ∃ η : (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙ F ⟶
        L ⋙ (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapDerivedCategory,
      ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ)
        (β : ((extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
            (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P) ⟶
          ((restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
            restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
              (.up ℤ)).obj
            (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj P)),
        (∀ (j : ℤ) (b : B) (p : P.X j),
          β.f j (b ⊗ₜ[R, algebraMap R B] p) =
            (algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b) ⊗ₜ[A,
              (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] p)) →
        F.map (((DerivedCategory.quotientCompQhIso _).app _ ≪≫
          (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P).inv) ≫
          δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            (((extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategoryFactors
              (.up ℤ)).hom.app _) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app _ ≫ DerivedCategory.Q.map β =
        η.app (DerivedCategory.Q.obj P) ≫
          (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
            restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapDerivedCategory.map
            (L.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
              ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
              DerivedCategory.Qh.map
                (((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
                  (algebraMap A (A ⊗[R] B)))).mapHomotopyCategoryFactors
                    (.up ℤ)).hom.app P) ≫
              (DerivedCategory.quotientCompQhIso _).hom.app _) ≫
          (Functor.mapDerivedCategoryFactors
            (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
              restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom)).hom.app _ := by
  have _hF := hF
  let r := restrictScalars.{u} (algebraMap R A)
  let e := extendScalars.{u, u, u} (algebraMap R B)
  let l := extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
    (algebraMap A (A ⊗[R] B)))
  let s := restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
    restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom
  obtain ⟨γ, hγ⟩ := exists_baseTensorCoefficientNaturalMap R A B D
  let γh : r.mapHomotopyCategory (.up ℤ) ⋙ e.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    CategoryTheory.Quotient.natTransLift _
      (Functor.whiskerRight γ (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh))
  let G := r.mapDerivedCategory ⋙ F
  let T := L ⋙ s.mapDerivedCategory
  let α : DerivedCategory.Qh ⋙ T ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε s.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (l.mapHomotopyCategory (.up ℤ))
        s.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv
  let : T.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    scalarExtensionDerivedRestriction _ s L ε hL
  let τ : DerivedCategory.Qh ⋙ G ⟶
      l.mapHomotopyCategory (.up ℤ) ⋙ s.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight r.mapDerivedCategoryFactorsh.hom F ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (r.mapHomotopyCategory (.up ℤ)) δ ≫
      (Functor.associator _ _ _).inv ≫ γh
  let η := T.leftDerivedLift α (HomotopyCategory.quasiIso _ (.up ℤ)) G τ
  refine ⟨η, ?_⟩
  intro P β hβ
  have hb : β = γ.app P := by
    ext j x
    induction x using TensorProduct.inductionOn with
    | tmul b p => exact (hβ j b p).trans (hγ P j b p).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  subst β
  have h := T.leftDerived_fac_app α (HomotopyCategory.quasiIso _ (.up ℤ)) G τ
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  dsimp only [η, α, τ, G, T, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app] at h
  simp only [Category.id_comp, Category.comp_id] at h
  have hr : r.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      r.mapDerivedCategoryFactors.hom.app P := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change r.mapDerivedCategory.map (𝟙 _) ≫ r.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [r.mapDerivedCategory.map_id (DerivedCategory.Q.obj P),
      DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj P))]
    simp only [Category.id_comp]
    exact Category.comp_id _
  have hs : s.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((l.mapHomologicalComplex (.up ℤ)).obj P)) =
      s.mapDerivedCategoryFactors.hom.app
        ((l.mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change s.mapDerivedCategory.map (𝟙 _) ≫ s.mapDerivedCategoryFactors.hom.app _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [s.mapDerivedCategory.map_id (DerivedCategory.Q.obj
        ((l.mapHomologicalComplex (.up ℤ)).obj P)),
      DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((s.mapHomologicalComplex (.up ℤ)).obj
          ((l.mapHomologicalComplex (.up ℤ)).obj P)))]
    simp only [Category.id_comp]
    exact Category.comp_id _
  change η.app (DerivedCategory.Q.obj P) ≫ s.mapDerivedCategory.map
      (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      s.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((l.mapHomologicalComplex (.up ℤ)).obj P)) =
    F.map (r.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ δ.app _ ≫
      DerivedCategory.Q.map (γ.app P) at h
  rw [hr, hs] at h
  have hqR : (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app
      ((r.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have he : (e.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((r.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have hqB : (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).hom.app
      ((e.mapHomologicalComplex (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj P)) = 𝟙 _ := rfl
  have hqA : (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app P = 𝟙 _ := rfl
  have hl : (l.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
  have hqD : (DerivedCategory.quotientCompQhIso (ModuleCat.{u} D)).hom.app
      ((l.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv]
  erw [hqR, he, hqB, hqA, hl, hqD]
  change F.map (r.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _) ≫
      δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((r.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ DerivedCategory.Q.map (γ.app P) =
    η.app (DerivedCategory.Q.obj P) ≫ s.mapDerivedCategory.map
      (L.map (𝟙 _) ≫ ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _) ≫ s.mapDerivedCategoryFactors.hom.app _
  have hmapQ : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((e.mapHomologicalComplex (.up ℤ)).obj
          ((r.mapHomologicalComplex (.up ℤ)).obj P)))) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hmapQ' : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((l.mapHomologicalComplex (.up ℤ)).obj P))) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hmapL : L.map (𝟙 (DerivedCategory.Q.obj P)) = 𝟙 _ := L.map_id _
  erw [hmapQ, hmapQ', hmapL]
  simp only [Category.id_comp, Category.comp_id]
  have hidγ : 𝟙 (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((e.mapHomologicalComplex (.up ℤ)).obj
          ((r.mapHomologicalComplex (.up ℤ)).obj P)))) ≫
      DerivedCategory.Q.map (γ.app P) = DerivedCategory.Q.map (γ.app P) :=
    Category.id_comp _
  have hidε : ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((l.mapHomologicalComplex (.up ℤ)).obj P))) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := Category.comp_id _
  erw [hidγ, hidε]
  exact h.symm

end ModuleCat
