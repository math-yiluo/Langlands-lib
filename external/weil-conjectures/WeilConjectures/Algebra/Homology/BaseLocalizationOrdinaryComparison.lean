/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.BaseLocalizationMap

/-! Ordinary comparison square for base localization.

Source: Stacks Project, perfect.tex, Tags 0DJ8 and 06Y6.
(blueprint: lem-pc-base-localization-ordinary-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Rp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra Rp A] [Algebra Rp B]
  [tRpA : IsScalarTower R Rp A] [tRpB : IsScalarTower R Rp B]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [Algebra A D] [Algebra B D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] B) D]
  [tBpD : IsScalarTower B (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

omit [Algebra A D] [Algebra B D] tAD tBD tApD tBpD in
include tRpA tRpB in
/-- Ordinary comparison commutes with localization of the tensor base.
Source: Stacks Project, perfect.tex, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-ordinary-comparison).

Proof: compose restriction-of-scalars composition with the ordinary localization
isomorphism `baseLocalizationTensorIso`, and conjugate by the two ordinaryIso
isomorphisms. This constructs psi and fixes its values on b tensor q.
The universal lift defining baseLocalizationDerivedMap satisfies leftDerived_fac.
Evaluate that equation at the restricted complex Q. Naturality of the counit
with respect to baseLocalizationInputIso gives the square before cohomology.
Apply B-linear homology and its homotopy/derived factorization isomorphisms.
The two comparison_eq equations and cancellation of cohomologyIso identify
its sides with the displayed formula. No localizedComparison is used, and
no flatness of D or invertibility of a comparison is required. -/
theorem exists_baseLocalization_ordinaryComparison
    (S : Submonoid R) [IsLocalization S Rp] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :
    let CL := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let CK := ((ModuleCat.extendScalars (algebraMap A (A ⊗[Rp] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let F := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let G := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom
    ∃ ψ : (F.mapHomologicalComplex (.up ℤ)).obj CL ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj CK,
      (∀ (j : ℤ) (b : B) (q : Q.X j),
        ψ.f j ((Algebra.TensorProduct.includeRight b : A ⊗[R] B)
          ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q) =
        (Algebra.TensorProduct.includeRight b : A ⊗[Rp] B)
          ⊗ₜ[A,algebraMap A (A ⊗[Rp] B)] q) ∧
      ∀ x : L.cohomology i,
        HomologicalComplex.homologyMap ψ i
          ((CL.sc i |>.mapHomologyIso F).inv (L.comparison i x)) =
        (CK.sc i |>.mapHomologyIso G).inv
          (K.comparison i (baseLocalizationCohomologyMap R Rp B A D S Q L K i x)) := by
  dsimp only
  let r := ModuleCat.restrictScalars.{u} (algebraMap R Rp)
  let c := ModuleCat.restrictScalarsComp' (algebraMap R Rp) (algebraMap Rp A)
    (algebraMap R A) (IsScalarTower.algebraMap_eq R Rp A)
  let z := (Functor.mapHomologicalComplexCompIso c.symm (.up ℤ)).symm
  let σ := ((extend R B).mapIso (z.app Q)) ≪≫
    (Functor.mapHomologicalComplexCompIso (baseLocalizationTensorIso R Rp B S)
      (.up ℤ)).app ((restrict Rp A).obj Q)
  let ψ := L.ordinaryIso.inv ≫ σ.hom ≫ K.ordinaryIso.hom
  refine ⟨ψ, ?_, ?_⟩
  · intro j b q
    let : Module R (Q.X j) := Module.compHom (Q.X j) (algebraMap R A)
    let : Module Rp (Q.X j) := Module.compHom (Q.X j) (algebraMap Rp A)
    have hi : L.ordinaryIso.inv.f j
        ((Algebra.TensorProduct.includeRight b : A ⊗[R] B)
          ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q) = b ⊗ₜ[R,algebraMap R B] q := by
      rw [← L.ordinaryIso_tmul]
      exact (((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) j).mapIso
        L.ordinaryIso).toLinearEquiv).symm_apply_apply _
    change K.ordinaryIso.hom.f j (σ.hom.f j (L.ordinaryIso.inv.f j _)) = _
    rw [hi]
    have hσ : σ.hom.f j (b ⊗ₜ[R,algebraMap R B] q) =
        b ⊗ₜ[Rp,algebraMap Rp B] q := by
      rfl
    rw [hσ, K.ordinaryIso_tmul]
  · intro x
    let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let πP := HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)
    let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
    let P := (restrict R A).obj Q
    let P' := (restrict Rp A).obj Q
    let η := baseLocalizationDerivedMap R Rp B A D S Q L K
    let v := (baseLocalizationInputIso R Rp A Q).hom
    let _ := K.universal
    have hη : Functor.whiskerLeft DerivedCategory.Qh η ≫ K.counit =
        baseLocalizationCounit R Rp B A D S Q L := by
      exact Functor.leftDerived_fac K.derived K.counit
        (HomotopyCategory.quasiIso (ModuleCat.{u} Rp) (.up ℤ)) _ _
    have hc : (L.derived.map v ≫ η.app (DerivedCategory.Qh.obj (πP.obj P'))) ≫
        K.counit.app (πP.obj P') =
      L.counit.app (πR.obj P) ≫ DerivedCategory.Qh.map (πB.map σ.hom) := by
      have hf := congrArg (fun t ↦ t.app (πP.obj P')) hη
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
      rw [Category.assoc, hf]
      have hv : v = DerivedCategory.Qh.map (πR.map (z.app Q).hom) ≫
          DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (.up ℤ)).inv.app P') ≫
          r.mapDerivedCategoryFactorsh.inv.app (πP.obj P') := by
        simp [v, baseLocalizationInputIso, baseLocalizationInputNatIso,
          Iso.app, z, c, r, P', πP, πR, Functor.isoWhiskerRight,
          Functor.isoWhiskerLeft]
      rw [hv, Functor.map_comp, Functor.map_comp]
      dsimp only [baseLocalizationCounit]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
        Category.id_comp, Category.assoc]
      have hcancel : L.derived.map (r.mapDerivedCategoryFactorsh.inv.app (πP.obj P')) ≫
          L.derived.map (r.mapDerivedCategoryFactorsh.hom.app (πP.obj P')) = 𝟙 _ := by
        rw [← L.derived.map_comp, Iso.inv_hom_id_app, L.derived.map_id]
      erw [reassoc_of% hcancel]
      have hid : (r.mapHomotopyCategoryFactors (.up ℤ)).inv.app P' = 𝟙 _ := rfl
      erw [hid, DerivedCategory.Qh.map_id, L.derived.map_id, Category.id_comp]
      have hn := L.counit.naturality (πR.map (z.app Q).hom)
      change L.derived.map (DerivedCategory.Qh.map (πR.map (z.app Q).hom)) ≫
          L.counit.app _ = L.counit.app (πR.obj P) ≫
          DerivedCategory.Qh.map (πB.map ((extend R B).map (z.app Q).hom)) at hn
      erw [reassoc_of% hn]
      simp only [σ, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
      rfl
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    have h1 := congrArg H.map hc
    simp only [Functor.map_comp] at h1
    have h2 := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.naturality
      (πB.map σ.hom)
    have h3 := (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} B) (.up ℤ) i).hom.naturality σ.hom
    let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let Y := ((ModuleCat.extendScalars (algebraMap A (A ⊗[Rp] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let F := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let G := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom
    have hB : F.map (L.comparison i) ≫ ((X.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ψ i =
      baseLocalizationCohomologyMap R Rp B A D S Q L K i ≫
        G.map (K.comparison i) ≫ ((Y.sc i).mapHomologyIso G).inv := by
      rw [← Category.assoc, L.comparison_eq, K.comparison_eq]
      dsimp only [baseLocalizationCohomologyMap, ψ]
      simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
        Iso.inv_hom_id_assoc]
      have ho : HomologicalComplex.homologyMap L.ordinaryIso.hom i ≫
          HomologicalComplex.homologyMap L.ordinaryIso.inv i = 𝟙 _ := by
        rw [← HomologicalComplex.homologyMap_comp, L.ordinaryIso.hom_inv_id,
          HomologicalComplex.homologyMap_id]
      rw [reassoc_of% ho]
      dsimp only [Functor.comp_map] at h2 h3
      change (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).map
          (πB.map σ.hom) ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ =
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ ≫
          HomologicalComplex.homologyMap σ.hom i at h3
      have hh := congrArg (fun a ↦ (L.cohomologyIso i).hom ≫ a ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
          (πB.obj ((extend Rp B).obj P')) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
          ((extend Rp B).obj P') ≫ HomologicalComplex.homologyMap K.ordinaryIso.hom i) h1
      simp only [Category.assoc] at hh
      rw [reassoc_of% h2, reassoc_of% h3] at hh
      exact hh.symm
    exact ConcreteCategory.congr_hom hB x


end RingTensorCohomology
