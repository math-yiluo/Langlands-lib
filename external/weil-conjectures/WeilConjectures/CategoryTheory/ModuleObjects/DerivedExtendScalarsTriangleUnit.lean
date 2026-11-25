/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangle

/-!

# The reduction triangle with the unit of the derived adjunction

Let `φ : R ⟶ S` be a morphism of commutative algebra objects such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact. The reduction triangle
`K --k--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]` of `Mod.exists_distinguished_zsmul_derivedExtendScalars` can be
chosen with second morphism the unit `K ⟶ D(comap φ) (S ⊗ᴸ_R K)` of the derived adjunction
`S ⊗ᴸ_R - ⊣ D(comap φ)` (`Mod.exists_distinguished_zsmul_derivedExtendMapDerivedCategoryUnit`),
which is natural in `K`.

The unit of the derived adjunction is computed on a complex `K` by the levelwise unit
`K ⟶ S ⊗_R K`, modulo the counit of the left derived functor
(`Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac`); on a K-flat complex of flat
modules this is the second morphism of the short exact sequence `0 ⟶ P --k--> P ⟶ S ⊗_R P ⟶ 0`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- If a distinguished triangle `T` is isomorphic, on its first three objects and first two
morphisms, to `A --f--> B --g--> C`, then `f, g` complete to a distinguished triangle. -/
lemma exists_distinguished_of_isos (T : Triangle D) (hT : T ∈ distTriang D) {A B C : D}
    (f : A ⟶ B) (g : B ⟶ C) (e₁ : T.obj₁ ≅ A) (e₂ : T.obj₂ ≅ B) (e₃ : T.obj₃ ≅ C)
    (h₁ : T.mor₁ ≫ e₂.hom = e₁.hom ≫ f) (h₂ : T.mor₂ ≫ e₃.hom = e₂.hom ≫ g) :
    ∃ h, Triangle.mk f g h ∈ distTriang D := by
  refine ⟨e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ e₁ e₂ e₃ h₁ h₂ ?_).symm⟩
  rw [Triangle.mk_mor₃, Iso.hom_inv_id_assoc]

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The unit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `K`,
followed by the counit of the derived extension of scalars and the comparison for the exact
restriction of scalars, is the levelwise unit `K ⟶ S ⊗_R K`. -/
lemma derivedExtendMapDerivedCategoryAdjunction_unit_app_fac
    (K : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Qh.obj K) ≫
        (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app K) ≫
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) := by
  have h₁ := (extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)
    |>.derivedη_fac_app
    (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ))
    (extendScalars φ).leftDerivedFunctorCounit (comap φ).rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app (comap φ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₄ := (comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((extendScalars φ).leftDerivedFunctorCounit.app K)
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₄]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
/-- The levelwise unit `P ⟶ S ⊗_R P` of complexes is the unit of the adjunction induced on
complexes. -/
lemma extendUnitComplexHom_eq (P : CochainComplex (Mod C R) ℤ) :
    extendUnitComplexHom φ P =
      ((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P := by
  ext i : 1
  exact (extendRestrictAdjunction_unit_app φ (P.X i)).symm

/-- **The reduction triangle, with the unit of the derived adjunction**: if
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, then for every `K ∈ D(Mod_R(C))` the unit
`K ⟶ D(comap φ) (S ⊗ᴸ_R K)` of `S ⊗ᴸ_R - ⊣ D(comap φ)` completes `K --k--> K` to a distinguished
triangle `K --k--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`. -/
theorem exists_distinguished_zsmul_derivedExtendMapDerivedCategoryUnit (k : ℤ)
    (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)
    (K : DerivedCategory (Mod C R)) :
    ∃ h : (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧,
      Triangle.mk (k • 𝟙 K) ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app K) h ∈
        distTriang (DerivedCategory (Mod C R)) := by
  obtain ⟨P, π, _, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have hS := shortExact_extendUnitComplexHom k w hφ P hflat
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let adj := derivedExtendMapDerivedCategoryAdjunction φ
  let q := HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)
  let e₁ : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₀ : DerivedCategory.Qh.obj (q.obj P) ≅ K :=
    (DerivedCategory.quotientCompQhIso (Mod C R)).app P ≪≫ e₁
  let X₃ := ((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let e₃' : (comap φ).mapDerivedCategory.obj
      ((extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Qh.obj (q.obj P))) ≅
      DerivedCategory.Qh.obj (q.obj X₃) :=
    (comap φ).mapDerivedCategory.mapIso
        (asIso ((extendScalars φ).leftDerivedFunctorCounit.app (q.obj P))) ≪≫
      (comap φ).mapDerivedCategoryFactorsh.app
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj (q.obj P))
  let e₃ : DerivedCategory.Q.obj X₃ ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) :=
    ((DerivedCategory.quotientCompQhIso (Mod C R)).app X₃).symm ≪≫ e₃'.symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso e₀)
  have hunit : adj.unit.app (DerivedCategory.Qh.obj (q.obj P)) =
      DerivedCategory.Qh.map (q.map (extendUnitComplexHom φ P)) ≫ e₃'.inv := by
    rw [Iso.eq_comp_inv, extendUnitComplexHom_eq,
      ← Adjunction.mapHomotopyCategory_unit_app_quotient]
    exact derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ (q.obj P)
  refine exists_distinguished_of_isos _ (DerivedCategory.triangleOfSES_distinguished hS) _ _
    e₁ e₁ e₃ ?_ ?_
  · simp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₁, Functor.map_zsmul,
      Functor.map_id, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    erw [Category.id_comp, Category.comp_id]
  · have key : e₁.hom ≫ adj.unit.app K =
        (DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P ≫
          adj.unit.app (DerivedCategory.Qh.obj (q.obj P)) ≫
            (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map e₀.hom) := by
      erw [adj.unit_naturality e₀.hom]
      simp only [e₀, Iso.trans_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
    have hq := (DerivedCategory.quotientCompQhIso (Mod C R)).hom.naturality
      (extendUnitComplexHom φ P)
    have hq' : DerivedCategory.Qh.map (q.map (extendUnitComplexHom φ P)) =
        (DerivedCategory.quotientCompQhIso (Mod C R)).hom.app P ≫
          DerivedCategory.Q.map (extendUnitComplexHom φ P) ≫
            (DerivedCategory.quotientCompQhIso (Mod C R)).inv.app X₃ := by
      erw [← reassoc_of% hq, Iso.hom_inv_id_app, Category.comp_id]
    rw [key, hunit, hq']
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rfl

end CategoryTheory.Mod
