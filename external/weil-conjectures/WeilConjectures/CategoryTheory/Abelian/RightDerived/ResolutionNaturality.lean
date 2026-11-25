/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Naturality of the computation of right derived functors by acyclic resolutions

Let `F : C ⥤ D` be a left exact additive functor and `ι : single₀ X ⟶ I`, `ι' : single₀ Y ⟶ J`
resolutions by `F`-acyclic objects. A morphism `φ : X ⟶ Y` and a cochain map `c : I ⟶ J`
compatible with the augmentations induce the same map
`R^q F X ≅ H^q(F I) ⟶ H^q(F J) ≅ R^q F Y`
(`CategoryTheory.Functor.rightDerivedObjIsoOfResolution_hom_naturality`).

In particular, the identification `H^q(F I) ≅ H^q(F J)` of the cohomology of two `F`-acyclic
resolutions of the same object does not depend on a choice of a cochain map between them
(`CategoryTheory.Functor.resolutionComparison`).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **Naturality of `Functor.rightDerivedObjIsoOfResolution`.** Let
`ι : single₀ X ⟶ I` and `ι' : single₀ Y ⟶ J` be resolutions by `F`-acyclic objects, `φ : X ⟶ Y`
and `c : I ⟶ J` a cochain map compatible with `φ` on the augmentations. Then
`R^q F φ` corresponds to `H^q(F c)`. -/
lemma rightDerivedObjIsoOfResolution_hom_naturality {X Y : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (ι' : (CochainComplex.single₀ C).obj Y ⟶ J) [QuasiIso ι']
    (hI : ∀ n, F.rightAcyclic (I.X n)) (hJ : ∀ n, F.rightAcyclic (J.X n))
    (φ : X ⟶ Y) (c : I ⟶ J) (comm : ι.f 0 ≫ c.f 0 = φ ≫ ι'.f 0) (q : ℕ) :
    (F.rightDerived q).map φ ≫ (F.rightDerivedObjIsoOfResolution ι' hJ q).hom =
      (F.rightDerivedObjIsoOfResolution ι hI q).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map c) q := by
  let PX := injectiveResolution X
  let PY := injectiveResolution Y
  let cX := InjectiveResolution.descOfQuasiIso (𝟙 X) PX ι
  let cY := InjectiveResolution.descOfQuasiIso (𝟙 Y) PY ι'
  let d := InjectiveResolution.desc φ PY PX
  have hcX := InjectiveResolution.descOfQuasiIso_commutes (𝟙 X) PX ι
  have hcY := InjectiveResolution.descOfQuasiIso_commutes (𝟙 Y) PY ι'
  have hd := InjectiveResolution.desc_commutes φ PY PX
  have ho : Homotopy (c ≫ cY) (cX ≫ d) :=
    CochainComplex.homotopyOfQuasiIso ι _ _ (by
      have e1 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hcY
      have e2 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hcX
      have e3 := congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) hd
      simp only [HomologicalComplex.comp_f] at e1 e2 e3 ⊢
      calc ι.f 0 ≫ c.f 0 ≫ cY.f 0 = φ ≫ ι'.f 0 ≫ cY.f 0 := by rw [← Category.assoc, comm,
              Category.assoc]
        _ = φ ≫ PY.ι.f 0 := by rw [e1]; simp
        _ = PX.ι.f 0 ≫ d.f 0 := by rw [e3]; simp
        _ = ι.f 0 ≫ cX.f 0 ≫ d.f 0 := by rw [reassoc_of% e2]; simp)
  have : QuasiIso ((F.mapHomologicalComplex _).map cY) :=
    F.quasiIso_map_of_rightAcyclic_nat cY hJ fun _ ↦ Functor.rightAcyclic_of_injective _
  have : QuasiIso ((F.mapHomologicalComplex _).map cX) :=
    F.quasiIso_map_of_rightAcyclic_nat cX hI fun _ ↦ Functor.rightAcyclic_of_injective _
  have hH := (F.mapHomotopy ho).homologyMap_eq q
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hH
  have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality φ PX PY d
    (InjectiveResolution.desc_commutes_zero φ PY PX) F q
  dsimp only [Functor.rightDerivedObjIsoOfResolution,
    InjectiveResolution.isoRightDerivedObjOfQuasiIso]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv,
    ← cancel_mono (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map cY) q)]
  simp only [Category.assoc]
  erw [IsIso.inv_hom_id, Category.comp_id]
  rw [hH, IsIso.inv_hom_id_assoc]
  exact hnat

/-- The comparison `H^q(F I) ≅ H^q(F J)` between the cohomologies of two resolutions of the same
object by `F`-acyclic objects, through `R^q F X`. -/
noncomputable def resolutionComparison {X : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (ι' : (CochainComplex.single₀ C).obj X ⟶ J) [QuasiIso ι']
    (hI : ∀ n, F.rightAcyclic (I.X n)) (hJ : ∀ n, F.rightAcyclic (J.X n)) (q : ℕ) :
    ((F.mapHomologicalComplex _).obj I).homology q ≅
      ((F.mapHomologicalComplex _).obj J).homology q :=
  (F.rightDerivedObjIsoOfResolution ι hI q).symm ≪≫ F.rightDerivedObjIsoOfResolution ι' hJ q

/-- The comparison of two `F`-acyclic resolutions is induced by any cochain map between them
which is compatible with the augmentations. -/
lemma resolutionComparison_hom_eq {X : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (ι' : (CochainComplex.single₀ C).obj X ⟶ J) [QuasiIso ι']
    (hI : ∀ n, F.rightAcyclic (I.X n)) (hJ : ∀ n, F.rightAcyclic (J.X n)) (c : I ⟶ J)
    (comm : ι.f 0 ≫ c.f 0 = ι'.f 0) (q : ℕ) :
    (F.resolutionComparison ι ι' hI hJ q).hom =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map c) q := by
  have h := F.rightDerivedObjIsoOfResolution_hom_naturality ι ι' hI hJ (𝟙 X) c
    (by rw [comm, Category.id_comp]) q
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [resolutionComparison, Iso.trans_hom, Iso.symm_hom, h, Iso.inv_hom_id_assoc]

end CategoryTheory.Functor
