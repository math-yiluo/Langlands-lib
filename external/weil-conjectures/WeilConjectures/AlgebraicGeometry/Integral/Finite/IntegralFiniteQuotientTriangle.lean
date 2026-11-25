/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Derived scalar triangles over a quotient coefficient ring
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem quotientRestrictionFull
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    (hφ : ∀ Z : C, Epi (φ ▷ Z)) :
    (Mod.comap φ : Mod C S ⥤ Mod C R).Full := by
  constructor
  intro M N f
  have := hφ M.X
  let g : M ⟶ N := Mod.Hom.mk' f.hom (by
    apply (cancel_epi (φ ▷ M.X)).mp
    have hf := (show IsModHom R f.hom from inferInstance).smul_hom
    change (φ ▷ M.X ≫ γ[S,M.X]) ≫ f.hom =
      R ◁ f.hom ≫ φ ▷ N.X ≫ γ[S,N.X] at hf
    change φ ▷ M.X ≫ γ[S,M.X] ≫ f.hom =
      φ ▷ M.X ≫ S ◁ f.hom ≫ γ[S,N.X]
    calc
      _ = (φ ▷ M.X ≫ γ[S,M.X]) ≫ f.hom := (Category.assoc _ _ _).symm
      _ = R ◁ f.hom ≫ φ ▷ N.X ≫ γ[S,N.X] := hf
      _ = (R ◁ f.hom ≫ φ ▷ N.X) ≫ γ[S,N.X] := (Category.assoc _ _ _).symm
      _ = (φ ▷ M.X ≫ S ◁ f.hom) ≫ γ[S,N.X] :=
        congrArg (fun z ↦ z ≫ γ[S,N.X]) (whisker_exchange φ f.hom)
      _ = _ := Category.assoc _ _ _)
  exact ⟨g, rfl⟩

/-- A short exact coefficient sequence yields a distinguished scalar-extension triangle
linear over its middle quotient ring. -/
theorem quotientScalarTriangle
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S T U : C} [MonObj R] [MonObj S] [MonObj T] [MonObj U]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T] [IsCommMonObj U]
    (q : R ⟶ S) (t : S ⟶ T) (s : S ⟶ U)
    [IsMonHom q] [IsMonHom t] [IsMonHom s]
    (hq : ∀ Z : C, Epi (q ▷ Z))
    (f : (Mod.comap (q ≫ t)).obj (Mod.regular T) ⟶
      (Mod.comap q).obj (Mod.regular S))
    (g : (Mod.comap q).obj (Mod.regular S) ⟶
      (Mod.comap (q ≫ s)).obj (Mod.regular U))
    (hz : f ≫ g = 0) (hs : (ShortComplex.mk f g hz).ShortExact)
    (K : DerivedCategory (Mod C R)) :
    ∃ Δ : CategoryTheory.Pretriangulated.Triangle (DerivedCategory (Mod C S)),
      Δ ∈ distTriang _ ∧
      Nonempty (Δ.obj₁ ≅ (Mod.comap t).mapDerivedCategory.obj
        ((Mod.extendScalars (q ≫ t)).leftDerivedFunctor.obj K)) ∧
      Nonempty (Δ.obj₂ ≅ (Mod.extendScalars q).leftDerivedFunctor.obj K) ∧
      Nonempty (Δ.obj₃ ≅ (Mod.comap s).mapDerivedCategory.obj
        ((Mod.extendScalars (q ≫ s)).leftDerivedFunctor.obj K)) := by
  classical
  obtain ⟨P, π, hπ, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have : QuasiIso π := hπ
  let eK := asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let B := ShortComplex.mk f g hz
  let L (M : Mod C R) := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  let α := (NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map f)
    (.up ℤ)).app P
  let β := (NatTrans.mapHomologicalComplex ((tensoringRight (Mod C R)).map g)
    (.up ℤ)).app P
  have hαβ : α ≫ β = 0 := by
    ext i : 1
    change (P.X i ◁ f) ≫ (P.X i ◁ g) = 0
    rw [← whiskerLeft_comp, hz, MonoidalPreadditive.whiskerLeft_zero]
  have hSES : (ShortComplex.mk α β hαβ).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    have := (hflat i).tensorLeft.preservesFiniteLimits
    exact hs.map_of_exact (tensorLeft (P.X i))
  let N₁ := ((Mod.comap t).mapHomologicalComplex (.up ℤ)).obj
    (((Mod.extendScalars (q ≫ t)).mapHomologicalComplex (.up ℤ)).obj P)
  let N₂ := ((Mod.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  let N₃ := ((Mod.comap s).mapHomologicalComplex (.up ℤ)).obj
    (((Mod.extendScalars (q ≫ s)).mapHomologicalComplex (.up ℤ)).obj P)
  let V : CochainComplex (Mod C S) ℤ ⥤ CochainComplex (Mod C R) ℤ :=
    (Mod.comap q).mapHomologicalComplex (.up ℤ)
  have : (Mod.comap q : Mod C S ⥤ Mod C R).Full := quotientRestrictionFull q hq
  let c (A : C) [MonObj A] [IsCommMonObj A] (r : R ⟶ A) [IsMonHom r] :=
    Mod.KFlatScalarTower.extendTensorRightNatIso r
  let c₁ : L B.X₁ ≅ V.obj N₁ :=
    (NatIso.mapHomologicalComplex (c T (q ≫ t)).symm (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Mod.comapComp q t).symm (.up ℤ)).app
        (((Mod.extendScalars (q ≫ t)).mapHomologicalComplex (.up ℤ)).obj P)).symm
  let c₂ : L B.X₂ ≅ V.obj N₂ :=
    (NatIso.mapHomologicalComplex (c S q).symm (.up ℤ)).app P
  let c₃ : L B.X₃ ≅ V.obj N₃ :=
    (NatIso.mapHomologicalComplex (c U (q ≫ s)).symm (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Mod.comapComp q s).symm (.up ℤ)).app
        (((Mod.extendScalars (q ≫ s)).mapHomologicalComplex (.up ℤ)).obj P)).symm
  let α' := c₁.inv ≫ α ≫ c₂.hom
  let β' := c₂.inv ≫ β ≫ c₃.hom
  have hw : α' ≫ β' = 0 := by
    simp only [α', β', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc α β, hαβ, zero_comp, comp_zero]
  have hS' : (ShortComplex.mk α' β' hw).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk c₁ c₂ c₃ (by simp [α']) (by simp [β'])) hSES
  obtain ⟨a, b, hab, hSab, _, _⟩ := SheafOfModules.lift_shortExact V α' β' hw hS'
  let Δ := DerivedCategory.triangleOfSES hSab
  have ec (A : C) [MonObj A] [IsCommMonObj A] (r : R ⟶ A) [IsMonHom r] :
      (Mod.extendScalars r).leftDerivedFunctor.obj K ≅
        DerivedCategory.Q.obj
          (((Mod.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P) := by
    have : IsIso ((Mod.KFlatScalarTower.computationCounit r).app P) := by
      have : IsIso ((Mod.extendScalars r).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient (Mod C R) (.up ℤ)).obj P)) :=
        (Mod.extendScalars r).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
      dsimp only [Mod.KFlatScalarTower.computationCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    exact (Mod.extendScalars r).leftDerivedFunctor.mapIso eK.symm ≪≫
      asIso ((Mod.KFlatScalarTower.computationCounit r).app P)
  refine ⟨Δ, DerivedCategory.triangleOfSES_distinguished hSab, ⟨?_⟩, ⟨(ec S q).symm⟩,
    ⟨?_⟩⟩
  · exact ((Mod.comap t).mapDerivedCategoryFactors.app _).symm ≪≫
      (Mod.comap t).mapDerivedCategory.mapIso (ec T (q ≫ t)).symm
  · exact ((Mod.comap s).mapDerivedCategoryFactors.app _).symm ≪≫
      (Mod.comap s).mapDerivedCategory.mapIso (ec U (q ≫ s)).symm

end AlgebraicGeometry.ProEtale
