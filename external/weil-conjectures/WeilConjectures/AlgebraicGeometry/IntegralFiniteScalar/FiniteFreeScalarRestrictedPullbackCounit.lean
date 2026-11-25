/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarPullbackCounit

/-! # Restricted scalar counits and exact pullback
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm

private instance map_monoid {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed
  Mod.monoidalCategoryStruct Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] derivedComapUpperStarIso comapUpperStarIso

-- Perform the diagram calculations with abstract objects, before specializing to sheaves.
private theorem scalarCounit_inverseSquare
    {V : Type*} [Category V] {A B C D E H : V}
    (e : A ≅ B) (p : D ≅ E) (u : A ⟶ C) (v : C ⟶ D) (w : B ⟶ H) (z : H ⟶ E)
    (h : u ≫ v ≫ p.hom = e.hom ≫ w ≫ z) :
    e.inv ≫ u ≫ v = w ≫ z ≫ p.inv := by
  apply (cancel_epi e.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id, Category.comp_id]

private theorem restrictedCounit_paste
    {V W T : Type*} [Category V] [Category W] [Category T]
    (R : V ⥤ W) (F : T ⥤ W)
    {A B C D E H : V} {U₀ U₁ U₂ : T} {Z₀ Z₁ Z₂ : W}
    (t : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (c' : A ⟶ E) (g : E ⟶ H) (p : H ⟶ D)
    (cY : U₀ ⟶ U₁) (rY : U₁ ⟶ U₂)
    (d₀ : F.obj U₀ ⟶ R.obj A) (d₁ : F.obj U₁ ⟶ R.obj E)
    (r₀ : R.obj H ⟶ Z₀) (r₁ : R.obj D ⟶ Z₂) (s : F.obj U₂ ⟶ Z₁)
    (q : Z₁ ⟶ Z₀) (p' : Z₀ ⟶ Z₂)
    (hp : t ≫ b ≫ c = c' ≫ g ≫ p)
    (hn : d₀ ≫ R.map c' = F.map cY ≫ d₁)
    (hq : d₁ ≫ R.map g ≫ r₀ = F.map rY ≫ s ≫ q)
    (hr : R.map p ≫ r₁ = r₀ ≫ p') :
    d₀ ≫ R.map t ≫ R.map b ≫ (R.map c ≫ r₁) =
      F.map (cY ≫ rY) ≫ s ≫ q ≫ p' := by
  have hp' := congrArg R.map hp
  simp only [Functor.map_comp] at hp'
  rw [reassoc_of% hp', hr, ← Category.assoc d₀, hn]
  simp only [Category.assoc]
  rw [reassoc_of% hq]
  simp only [Functor.map_comp, Category.assoc]

-- Compute the scalar mate before using any K-flat invertibility.
/-- Restricted scalar counits commute with exact geometric pullback and the normalized
scalar mate. -/
theorem finiteFreeScalar_restrictedCounit_pullback
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let EC := ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
        (.up ℤ)).obj C
    let p := (NatTrans.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
    let q := (NatTrans.mapHomologicalComplex
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
        ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map
        ((scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C)) ≫
      ((restriction a X).map (scalarCounit a X FC) ≫
        (Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
            (.up ℤ)).obj FC)) =
    (scalarSixPull Λ f).map (((restriction a Y).map (scalarCounit a Y C) ≫
        (Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapDerivedCategoryFactors.hom.app
            EC)) ≫
      F.mapDerivedCategoryFactors.hom.app
        (((Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
            (.up ℤ)).obj EC) ≫
      DerivedCategory.Q.map q ≫
      DerivedCategory.Q.map
        (((Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
            (.up ℤ)).map p) := by
  dsimp only
  let F := CondensedRing.upperStar Λ.X f
  let G := CondensedRing.upperStar Λ'.X f
  let RX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  let EC := ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
        (.up ℤ)).obj C
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let p := (NatTrans.mapHomologicalComplex
    (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
  let q := (NatTrans.mapHomologicalComplex
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
  let d := derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
  have hp : (D.theta a f).inv.app (DerivedCategory.Q.obj C) ≫
      (scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C) ≫
      scalarCounit a X FC =
    (scalarSixPull Λ' f).map (scalarCounit a Y C) ≫
      G.mapDerivedCategoryFactors.hom.app EC ≫ DerivedCategory.Q.map p := by
    let e := (NatIso.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) (.up ℤ)).app C
    have h := scalarCounit_inverseSquare ((D.theta a f).app (DerivedCategory.Q.obj C))
      (DerivedCategory.Q.mapIso e)
      ((scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C))
      (scalarCounit a X FC) ((scalarSixPull Λ' f).map (scalarCounit a Y C))
      (G.mapDerivedCategoryFactors.hom.app EC)
      (finiteFreeScalar_pullback_scalarCounit D a f C)
    exact h
  have hq := Functor.exactSquare_fac
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm EC
  rw [Functor.square_symm_hom] at hq
  have hd : d = Functor.mapDerivedCategorySquareIso
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) := by
    dsimp only [d]
    delta CondensedRing.derivedComapUpperStarIso Functor.mapDerivedCategorySquareIso
    rfl
  rw [← hd] at hq
  have hn := d.inv.naturality (scalarCounit a Y C)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  exact restrictedCounit_paste RX.mapDerivedCategory F.mapDerivedCategory
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hn.symm hq
    (RX.mapDerivedCategoryFactors_hom_naturality p)

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
