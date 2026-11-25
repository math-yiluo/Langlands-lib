/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison

/-! # Normalized total tensor comparison for pro-etale scalar extension

## References

* Stacks 03EL and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.completedAdicChangeData
  AlgebraicGeometry.Scheme.pbcScalarAdjunction
  SheafOfModules.CochainScalarConstruction.tensorUnit

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

open CategoryTheory.MonoidalCategory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
open SheafOfModules.CochainScalarConstruction

section TensorCalculation

private theorem proEt_small (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance 3100] proEt_small
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.cochainModulesPreadditive

private theorem ordinary_tensor (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃ e : ∀ M N : pbcModules X A,
      (pbcExtend φ).obj ((SheafOfModules.monoidalCategory A).tensorObj M N) ≅
        (SheafOfModules.monoidalCategory B).tensorObj
          ((pbcExtend φ).obj M) ((pbcExtend φ).obj N),
      (∀ {M M' N N' : pbcModules X A} (f : M ⟶ M') (g : N ⟶ N'),
        (pbcExtend φ).map ((SheafOfModules.monoidalCategory A).tensorHom f g) ≫
          (e M' N').hom = (e M N).hom ≫
          (SheafOfModules.monoidalCategory B).tensorHom
            ((pbcExtend φ).map f) ((pbcExtend φ).map g)) ∧
      ∀ M N U x y, (e M N).hom.val.app U
        (pbcTensorSection φ _ U 1 (pure A M N U x y)) =
        pure B _ _ U (pbcTensorSection φ M U 1 x) (pbcTensorSection φ N U 1 y) := by
  classical
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.monoidalCategory B
  let F := pbcExtend φ
  let G : pbcModules X A ⥤ pbcModules X B :=
    SheafOfModules.CochainScalarConstruction.tensorFunctor (K := ProEt.topology X) φ
  let j : F ≅ G := NatIso.ofComponents
    (fun M ↦ eqToIso (reductionChange_obj_eq X φ M)) (by
      intro M N f
      change F.map f ≫ eqToHom (reductionChange_obj_eq X φ N) =
        eqToHom (reductionChange_obj_eq X φ M) ≫ SheafOfModules.changeOfRingsHom φ M f
      rw [reductionChange_map_eq]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  obtain ⟨e₀, hn₀, hp₀⟩ :=
    SheafOfModules.CochainScalarConstruction.exists_scalarTensorComparison φ
  let e₀' : tensor _ ⋙ G ≅ (G.prod G) ⋙ tensor _ :=
    NatIso.ofComponents (fun Z ↦ e₀ Z.1 Z.2) (fun f ↦ hn₀ f.1 f.2)
  let e' : tensor _ ⋙ F ≅ (F.prod F) ⋙ tensor _ :=
    isoWhiskerLeft (tensor _) j ≪≫ e₀' ≪≫
      isoWhiskerRight (NatIso.prod j.symm j.symm) (tensor _)
  have hu (M : pbcModules X A) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
      (j.hom.app M).val.app U (pbcTensorSection φ M U 1 x) =
        (SheafOfModules.CochainScalarConstruction.tensorUnit φ M).hom.app U x := by
    trans (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U
            ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))
    · change (eqToHom (reductionChange_obj_eq X φ M)).val.app U
        ((eqToHom (reductionChange_obj_eq X φ M).symm).val.app U _) = _
      have hi := congrArg (fun f ↦ f.val.app U
        ((toSheafify (ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x)))
        (eqToIso (reductionChange_obj_eq X φ M)).inv_hom_id
      exact hi
    · exact (SheafOfModules.CochainScalarConstruction.tensorUnit_apply φ M U x).symm
  have hui (M : pbcModules X A) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
      (j.inv.app M).val.app U
        ((SheafOfModules.CochainScalarConstruction.tensorUnit φ M).hom.app U x) =
          pbcTensorSection φ M U 1 x := by
    rw [← hu]
    exact congrArg (fun f ↦ f.val.app U (pbcTensorSection φ M U 1 x)) (j.app M).hom_inv_id
  refine ⟨fun M N ↦ e'.app (M, N), ?_, ?_⟩
  · intro M M' N N' f g
    exact e'.hom.naturality (Prod.mkHom f g)
  · intro M N U x y
    change ((SheafOfModules.monoidalCategory B).tensorHom (j.inv.app M) (j.inv.app N)).val.app U
      ((e₀ M N).hom.val.app U ((j.hom.app _).val.app U
        (pbcTensorSection φ _ U 1 (pure A M N U x y)))) = _
    rw [hu]
    have hp := hp₀ M N U x y
    change (e₀ M N).hom.val.app U _ = pure B _ _ U _ _ at hp
    have hm := SheafOfModules.CochainScalarConstruction.pure_map B
      (j.inv.app M) (j.inv.app N) U
      ((SheafOfModules.CochainScalarConstruction.tensorUnit φ M).hom.app U x)
      ((SheafOfModules.CochainScalarConstruction.tensorUnit φ N).hom.app U y)
    exact (congrArg
      (((SheafOfModules.monoidalCategory B).tensorHom (j.inv.app M) (j.inv.app N)).val.app U)
      hp).trans (hm.trans (congrArg₂ (pure B _ _ U) (hui M U x) (hui N U y)))

private theorem section_smul (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (M : pbcModules X A) (U : X.ProEtᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection φ M U s x = s • pbcTensorSection φ M U 1 x := by
  change completedAdicChangeTensor X φ M U s x =
    s • completedAdicChangeTensor X φ M U 1 x
  simpa only [mul_one] using completedTensor_smul X φ M U s 1 x

private theorem section_naturality (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B)
    {M N : pbcModules X A} (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    pbcTensorSection φ N U 1 (f.val.app U x) =
      ((pbcExtend φ).map f).val.app U (pbcTensorSection φ M U 1 x) := by
  have h := congrArg (fun g ↦ g.val.app U x)
    ((pbcScalarAdjunction φ).unit.naturality f)
  change ((pbcScalarAdjunction φ).unit.app N).val.app U (f.val.app U x) =
    ((pbcExtend φ).map f).val.app U (((pbcScalarAdjunction φ).unit.app M).val.app U x) at h
  have hu (M : pbcModules X A) (x : M.val.obj U) :
      ((pbcScalarAdjunction φ).unit.app M).val.app U x =
        pbcTensorSection φ M U 1 x := by
    unfold pbcScalarAdjunction
    exact (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  rw [hu, hu] at h
  exact h

private theorem pure_smul (X : Scheme.{u})
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : pbcModules X B) (U : X.ProEtᵒᵖ) (s : B.obj.obj U)
    (x : M.val.obj U) (y : N.val.obj U) :
    pure B M N U (s • x) y = s • pure B M N U x y :=
  (SheafOfModules.CochainScalarConstruction.pureBilin B M N U).map_smul₂ s x y

private theorem generator_smul (X : Scheme.{u})
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (pbcModules X B) ℤ) (p q : ℤ) (U : X.ProEtᵒᵖ)
    (s : B.obj.obj U) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) B
      P Q p q (p + q) rfl U (s • x) y =
    s • coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) B
      P Q p q (p + q) rfl U x y := by
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.cochainModulesPreadditive B
  change (CochainComplex.ιMapBifunctor P Q (curriedTensor (pbcModules X B))
    p q (p + q) rfl).val.app U (pure B _ _ U (s • x) y) =
      s • (CochainComplex.ιMapBifunctor P Q (curriedTensor (pbcModules X B))
        p q (p + q) rfl).val.app U (pure B _ _ U x y)
  rw [pure_smul, _root_.map_smul]

private theorem total_balance_unit (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (e : ∀ M N : pbcModules X A,
      (pbcExtend φ).obj ((SheafOfModules.monoidalCategory A).tensorObj M N) ≅
        (SheafOfModules.monoidalCategory B).tensorObj
          ((pbcExtend φ).obj M) ((pbcExtend φ).obj N))
    (hgen : ∀ M N U x y, (e M N).hom.val.app U
      (pbcTensorSection φ _ U 1 (pure A M N U x y)) =
        pure B _ _ U (pbcTensorSection φ M U 1 x) (pbcTensorSection φ N U 1 y))
    (b₀ : (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).prod
        ((pbcExtend φ).mapHomologicalComplex (.up ℤ))) ⋙
          coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) B ≅
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) A ⋙
        (pbcExtend φ).mapHomologicalComplex (.up ℤ))
    (hb₀ : ∀ (P Q : CochainComplex (pbcModules X A) ℤ) (n : ℤ),
      (b₀.hom.app (P, Q)).f n =
        CategoryTheory.tensorPullbackTotalComponent (pbcExtend φ) e P Q n)
    (P Q : CochainComplex (pbcModules X A) ℤ) (p q : ℤ)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((b₀.inv.app (P, Q)).f (p + q)).val.app U
      (pbcTensorSection φ _ U 1
        (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) A
          P Q p q (p + q) rfl U x y)) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) B
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q) p q (p + q) rfl U
      (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y) := by
  let L := pbcExtend φ
  let F := L.mapHomologicalComplex (.up ℤ)
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor (pbcModules X A))
    p q (p + q) rfl
  let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q)
    (curriedTensor (pbcModules X B)) p q (p + q) rfl
  let z := (HomologicalComplex.eval (pbcModules X B) (.up ℤ) (p + q)).mapIso
    (b₀.app (P, Q))
  have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ L.map ι := by
    change ι' ≫ (b₀.hom.app (P, Q)).f (p + q) = _
    rw [hb₀]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q rfl
  have hi : L.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
    apply (cancel_mono z.hom).mp
    erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
      Iso.hom_inv_id_assoc]
  have hn := section_naturality X φ ι U (pure A (P.X p) (Q.X q) U x y)
  have hh := congrArg (fun f ↦ f.val.app U
    (pbcTensorSection φ _ U 1 (pure A (P.X p) (Q.X q) U x y))) hi
  change z.inv.val.app U
    (pbcTensorSection φ _ U 1 (ι.val.app U (pure A (P.X p) (Q.X q) U x y))) =
      ι'.val.app U (pure B _ _ U
        (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y))
  clear_value z
  change z.inv.val.app U ((L.map ι).val.app U
    (pbcTensorSection φ _ U 1 (pure A (P.X p) (Q.X q) U x y))) =
      ι'.val.app U ((e (P.X p) (Q.X q)).hom.val.app U
        (pbcTensorSection φ _ U 1 (pure A (P.X p) (Q.X q) U x y))) at hh
  have hgen' := hgen (P.X p) (Q.X q) U x y
  exact (congrArg (z.inv.val.app U) hn).trans
    (hh.trans (congrArg (ι'.val.app U) hgen'))

end TensorCalculation

/-- Scalar extension commutes with total tensor, with its scalar-first section formula. -/
theorem pbc_tensor_balance_exists (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃ balance : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) A ⋙
        (pbcExtend φ).mapHomologicalComplex (.up ℤ) ≅
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).prod
        ((pbcExtend φ).mapHomologicalComplex (.up ℤ))) ⋙
          coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) B,
      ∀ (P Q : CochainComplex (pbcModules X A) ℤ) (p q : ℤ) (U : X.ProEtᵒᵖ)
          (s : B.obj.obj U) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((balance.hom.app (P, Q)).f (p + q)).val.app U
          (pbcTensorSection φ _ U s
            (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) A
              P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) B
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q) p q (p + q) rfl U
          (pbcTensorSection φ (P.X p) U s x) (pbcTensorSection φ (Q.X q) U 1 y) := by
  classical
  let L := pbcExtend φ
  let F := L.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.cochainModulesPreadditive A
  let := SheafOfModules.cochainModulesPreadditive B
  let tA := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) A
  let tB := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) B
  obtain ⟨e, he, hgen⟩ := ordinary_tensor X φ
  have hiso (P Q : CochainComplex (pbcModules X A) ℤ) :
      IsIso (CategoryTheory.tensorPullbackTotal L e he P Q) :=
    CategoryTheory.tensorPullbackTotal_isIso L e he (pbcRestrict φ)
      (pbcScalarAdjunction φ) P Q
  let b₀ : (F.prod F) ⋙ tB ≅ tA ⋙ F := NatIso.ofComponents
    (fun Z ↦ @asIso _ _ _ _ (CategoryTheory.tensorPullbackTotal L e he Z.1 Z.2)
      (hiso Z.1 Z.2)) (by
        intro Z Z' f
        dsimp only [F, tA, tB, Functor.comp_map, Functor.prod_map]
        simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex,
          asIso_hom, CategoryTheory.ScalarHomTensor.tensorMap_factor]
        exact CategoryTheory.ScalarHomTensor.tensorPullbackTotal_naturality L e he f.1 f.2)
  have hb₀ (P Q : CochainComplex (pbcModules X A) ℤ) (n : ℤ) :
      ((b₀.hom.app (P, Q)).f n) =
        CategoryTheory.tensorPullbackTotalComponent L e P Q n := rfl
  clear_value b₀
  let b := b₀.symm
  have hg := total_balance_unit X φ e hgen b₀ hb₀
  refine ⟨b, ?_⟩
  intro P Q p q U s x y
  rw [section_smul, _root_.map_smul]
  have h := congrArg (fun z ↦ s • z) (hg P Q p q U x y)
  refine h.trans ?_
  have hs := congrArg (fun z ↦
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) B
      (F.obj P) (F.obj Q) p q (p + q) rfl U z
      (pbcTensorSection φ (Q.X q) U 1 y))
    (section_smul X φ (P.X p) U s x)
  exact (hs.trans (generator_smul X B (F.obj P) (F.obj Q) p q U s
    (pbcTensorSection φ (P.X p) U 1 x) (pbcTensorSection φ (Q.X q) U 1 y))).symm

end AlgebraicGeometry.Scheme
