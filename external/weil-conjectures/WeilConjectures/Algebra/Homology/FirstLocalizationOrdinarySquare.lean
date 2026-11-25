/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FirstLocalizationMap

/-! # Comparison square for the characterized localization map

Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-first-localization-ordinary-square). -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Aq D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Aq] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [tRA : IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

private theorem map_homology_pi {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

private theorem forget_restrict_cyclesIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapCyclesIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapCyclesIso (ModuleCat.restrictScalars f)).hom =
    (S.mapCyclesIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_mono ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).map S.iCycles)).1
  simp only [Category.assoc]
  rw [← ModuleCat.forget₂_map_restrictScalars f S.iCycles]
  rw [← Functor.map_comp, ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ModuleCat.forget₂_map_restrictScalars, ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

private theorem forget_restrict_homologyIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapHomologyIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapHomologyIso (ModuleCat.restrictScalars f)).hom =
    (S.mapHomologyIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_epi (((S.map (ModuleCat.restrictScalars f)).map
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).homologyπ)).1
  rw [← Category.assoc, map_homology_pi (S.map (ModuleCat.restrictScalars f))
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})]
  simp only [Category.assoc]
  rw [← Functor.map_comp, map_homology_pi, Functor.map_comp]
  rw [← Category.assoc, forget_restrict_cyclesIso]
  rw [ModuleCat.forget₂_map_restrictScalars]
  exact (map_homology_pi S (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).symm

private theorem forget_comparison_transport
    (B E : Type u) [CommRing B] [CommRing E] (f : B →+* E)
    (M : ModuleCat.{u} E) (X : CochainComplex (ModuleCat.{u} E) ℤ)
    (i : ℤ) (a : M ⟶ X.homology i) :
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map a ≫
      ((X.sc i).mapHomologyIso (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).inv =
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      ((ModuleCat.restrictScalars f).map a ≫
        ((X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).inv) ≫
      (((X.sc i).map (ModuleCat.restrictScalars f)).mapHomologyIso
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).inv := by
  let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let qE := (X.sc i).mapHomologyIso UE
  let qR := (X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)
  let qB := ((X.sc i).map (ModuleCat.restrictScalars f)).mapHomologyIso UB
  have he : qB ≪≫ UB.mapIso qR = qE := by
    apply Iso.ext
    exact forget_restrict_homologyIso B E f (X.sc i)
  have hi := congrArg (fun e ↦ e.inv) he
  simp only [Iso.trans_inv, Functor.mapIso_inv] at hi
  simp only [Functor.map_comp, ModuleCat.forget₂_map_restrictScalars, Category.assoc]
  exact congrArg (fun k ↦ UE.map a ≫ k) hi.symm

private theorem ordinary_B_square (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D) :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom)).inv ≫
      HomologicalComplex.homologyMap
        (L.ordinaryIso.inv ≫ ((ModuleCat.extendScalars
          (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map (firstLocalizationUnit R A Aq Q) ≫
            K.ordinaryIso.hom) i =
    firstLocalizationCohomologyMap R A Aq B D Q L K i ≫
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).map
          (K.comparison i) ≫
        (((((ModuleCat.extendScalars (algebraMap Aq (Aq ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj ((extend A Aq).obj Q)).sc i).mapHomologyIso
            (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom)).inv := by
  let _ := L.universal
  let _ := K.universal
  let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let P := (restrict R A).obj Q
  let G := (restrict R Aq).obj ((extend A Aq).obj Q)
  let u := firstLocalizationUnit R A Aq Q
  let t := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map u
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  have hfac : ζ.hom.app (DerivedCategory.Qh.obj (πR.obj G)) ≫
      K.counit.app (πR.obj G) = L.counit.app (πR.obj G) := by
    simp [ζ]
  have hc : L.derived.map (DerivedCategory.Qh.map (πR.map u)) ≫
      ζ.hom.app (DerivedCategory.Qh.obj (πR.obj G)) ≫ K.counit.app (πR.obj G) =
      L.counit.app (πR.obj P) ≫ DerivedCategory.Qh.map (πB.map t) := by
    rw [hfac]
    exact L.counit.naturality (πR.map u)
  have h1 := congrArg H.map hc
  simp only [Functor.map_comp] at h1
  have h2 := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.naturality
    (πB.map t)
  have h3 := (HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u} B) (.up ℤ) i).hom.naturality t
  rw [← Category.assoc, L.comparison_eq, K.comparison_eq]
  dsimp only [firstLocalizationCohomologyMap]
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  have ho : HomologicalComplex.homologyMap L.ordinaryIso.hom i ≫
      HomologicalComplex.homologyMap L.ordinaryIso.inv i = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, L.ordinaryIso.hom_inv_id,
      HomologicalComplex.homologyMap_id]
  rw [reassoc_of% ho]
  dsimp only [Functor.comp_map] at h2 h3
  change (HomotopyCategory.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).map (πB.map t) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app _ ≫
      HomologicalComplex.homologyMap t i at h3
  have hh := congrArg (fun a ↦ (L.cohomologyIso i).hom ≫ a ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
      (πB.obj (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
        (.up ℤ)).obj G)) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj G) ≫
    HomologicalComplex.homologyMap K.ordinaryIso.hom i) h1
  simp only [Category.assoc] at hh
  rw [reassoc_of% h2, reassoc_of% h3] at hh
  exact hh.symm

/-- Naturality of the ordinary comparison under the first-factor unit, after
forgetting scalar actions. Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-ordinary-square).

Proof: install the universal derived-functor instances of L and K. Their unique
comparison zeta intertwines the two counits. Apply counit naturality to
firstLocalizationUnit and then degree-i homology. Naturality of the two homotopy
and derived localization factorization isomorphisms identifies its ordinary side
with homology of extension of scalars applied to the unit. Substitute comparison_eq
for L and K, cancel cohomologyIso and ordinaryIso, and forget the B-action.
The natural homology isomorphism for exact restriction and forgetting scalars
identifies both resulting endpoints with the displayed additive homology objects.
No flatness, localization assumption, D-action compatibility or invertibility of
comparison is used. For identity units and zero complexes it is the same
naturality equation. -/
theorem firstLocalization_ordinary_square (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D) :
    (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).map (L.comparison i) ≫
      (((((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
          (forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u})).inv ≫
      HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map
          (L.ordinaryIso.inv ≫ ((ModuleCat.extendScalars
            (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map (firstLocalizationUnit R A Aq Q) ≫
              K.ordinaryIso.hom)) i =
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      (firstLocalizationCohomologyMap R A Aq B D Q L K i) ≫
      (forget₂ (ModuleCat.{u} (Aq ⊗[R] B)) AddCommGrpCat.{u}).map (K.comparison i) ≫
        (((((ModuleCat.extendScalars (algebraMap Aq (Aq ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).obj ((extend A Aq).obj Q)).sc i).mapHomologyIso
            (forget₂ (ModuleCat.{u} (Aq ⊗[R] B)) AddCommGrpCat.{u})).inv := by
  let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let Y := ((ModuleCat.extendScalars (algebraMap Aq (Aq ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj ((extend A Aq).obj Q)
  let f := (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let g := (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let φB := L.ordinaryIso.inv ≫ ((ModuleCat.extendScalars
    (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map
      (firstLocalizationUnit R A Aq Q) ≫ K.ordinaryIso.hom
  have hL := forget_comparison_transport B (A ⊗[R] B) f
    (L.cohomology i) X i (L.comparison i)
  have hK := forget_comparison_transport B (Aq ⊗[R] B) g
    (K.cohomology i) Y i (K.comparison i)
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℤ) i).map φB) UB
  have hb := ordinary_B_square R A B Aq D i Q L K
  have hh := congrArg UB.map hb
  simp only [Functor.map_comp] at hh
  rw [← Category.assoc, hL, hK]
  change UB.map (HomologicalComplex.homologyMap φB i) ≫
      (((Y.sc i).map (ModuleCat.restrictScalars g)).mapHomologyIso UB).inv =
    (((X.sc i).map (ModuleCat.restrictScalars f)).mapHomologyIso UB).inv ≫
      HomologicalComplex.homologyMap
        ((UB.mapHomologicalComplex (.up ℤ)).map φB) i at hn
  simp only [Category.assoc]
  calc
    _ = UB.map ((ModuleCat.restrictScalars f).map (L.comparison i) ≫
        ((X.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).inv) ≫
      UB.map (HomologicalComplex.homologyMap φB i) ≫
        (((Y.sc i).map (ModuleCat.restrictScalars g)).mapHomologyIso UB).inv := by
      exact congrArg (fun k ↦ UB.map ((ModuleCat.restrictScalars f).map
        (L.comparison i) ≫ ((X.sc i).mapHomologyIso
          (ModuleCat.restrictScalars f)).inv) ≫ k) hn.symm
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg (fun k ↦ k ≫
        (((Y.sc i).map (ModuleCat.restrictScalars g)).mapHomologyIso UB).inv) hh


end RingTensorCohomology
