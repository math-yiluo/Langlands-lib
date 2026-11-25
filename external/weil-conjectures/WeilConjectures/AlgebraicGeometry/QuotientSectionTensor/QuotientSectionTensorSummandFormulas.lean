/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors

/-! # Tensor comparison summand formulas

## References

* Stacks, Cohomology on Sites, Tag 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
private theorem paste_summand_square
    (E : A ⥤ C) (E' : B ⥤ D) (F : A ⥤ B) (F' : C ⥤ D)
    (a : F ⋙ E' ≅ E ⋙ F') {x T : A} {b B₀ : B} {c C₀ : C} {d d' U V : D}
    (j : x ⟶ T) (i : F.obj T ⟶ B₀) (t : E.obj T ⟶ C₀)
    (t' : E'.obj B₀ ⟶ U) (s : F'.obj C₀ ⟶ V) (e : U ⟶ V)
    (di : F.obj x ⟶ b) (d₀ : E.obj x ⟶ c)
    (d₁ : E'.obj b ⟶ d) (ds : F'.obj c ⟶ d')
    (jF : b ⟶ B₀) (jE : c ⟶ C₀) (jEF : d ⟶ U) (jFE : d' ⟶ V) (v : d ⟶ d')
    (hi : F.map j ≫ i = di ≫ jF) (ht : E.map j ≫ t = d₀ ≫ jE)
    (ht' : E'.map jF ≫ t' = d₁ ≫ jEF) (hs : F'.map jE ≫ s = ds ≫ jFE)
    (he : jEF ≫ e = v ≫ jFE)
    (ho : E'.map di ≫ d₁ ≫ v = a.hom.app x ≫ F'.map d₀ ≫ ds) :
    E'.map (F.map j) ≫ E'.map i ≫ t' ≫ e =
      E'.map (F.map j) ≫ a.hom.app T ≫ F'.map t ≫ s := by
  rw [← E'.map_comp_assoc, hi, E'.map_comp, Category.assoc, reassoc_of% ht', he]
  rw [reassoc_of% (a.hom.naturality j)]
  change _ = a.hom.app x ≫ F'.map (E.map j) ≫ F'.map t ≫ s
  rw [← F'.map_comp_assoc, ht, F'.map_comp, Category.assoc, hs]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ jFE) ho

end

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem summand_naturality (T : Scheme.{u})
    (F₁ : ModuleRingedComparison.internalModules Λ T ⥤
      ModuleRingedComparison.internalModules Λ' T)
    (F₂ : ModuleRingedComparison.internalModules Λ' T ⥤ ModuleRingedComparison.modules Λ' T)
    (G₁ : ModuleRingedComparison.internalModules Λ T ⥤ ModuleRingedComparison.modules Λ T)
    (G₂ : ModuleRingedComparison.modules Λ T ⥤ ModuleRingedComparison.modules Λ' T)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules Λ T) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    let F₁c := F₁.mapHomologicalComplex (.up ℤ)
    let F₂c := F₂.mapHomologicalComplex (.up ℤ)
    let G₁c := G₁.mapHomologicalComplex (.up ℤ)
    let G₂c := G₂.mapHomologicalComplex (.up ℤ)
    let eC : F₁c ⋙ F₂c ≅ G₁c ⋙ G₂c := NatIso.mapHomologicalComplex e (.up ℤ)
    HomologicalComplex.ιTensorObj (F₂c.obj (F₁c.obj P)) (F₂c.obj (F₁c.obj Q)) p q n hpq ≫
      ((eC.hom.app P ⊗ₘ eC.hom.app Q).f n) =
    (e.hom.app (P.X p) ⊗ₘ e.hom.app (Q.X q)) ≫
      HomologicalComplex.ιTensorObj (G₂c.obj (G₁c.obj P)) (G₂c.obj (G₁c.obj Q))
        p q n hpq := by
  dsimp only
  change GradedObject.Monoidal.ιTensorObj _ _ p q n hpq ≫
    GradedObject.Monoidal.tensorHom _ _ n = _
  rw [GradedObject.Monoidal.ι_tensorHom]
  rfl

/-- The specified total tensor comparison on each direct-sum summand.
This is the defining summand property of totalComparison, selected by its unique
normalized universal property. The private helpers express termwise tensor
naturality and elementary pasting without expanding the concrete tensor data. -/
theorem section_tensor_total_summand
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) (P Q : CochainComplex (ModuleRingedComparison.internalModules Λ Z) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (ModuleRingedComparison.equivalence Λ Z).functor.map
        (HomologicalComplex.ιTensorObj P Q p q n hpq) ≫
      (ModuleRingedComparison.totalComparison Λ Z P Q).hom.f n =
    (ModuleRingedComparison.ordinaryTensorComparison Λ Z (P.X p) (Q.X q)).hom ≫
      HomologicalComplex.ιTensorObj
        (((ModuleRingedComparison.equivalence Λ Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)
        (((ModuleRingedComparison.equivalence Λ Z).functor.mapHomologicalComplex
          (.up ℤ)).obj Q) p q n hpq := by
  exact (ModuleRingedComparison.totalComparison_existsUnique Λ Z P Q).exists.choose_spec
    p q n hpq

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem scalar_total_summand (T : Scheme.{u})
    (P Q : CochainComplex (Modules Λ T) ℤ) (i j n : ℤ) (h : i + j = n) :
    let := CondensedRing.internalScalarMonoidal a T
    let F := extension a T
    F.map (HomologicalComplex.ιTensorObj P Q i j n h) ≫ (totalScalar a T P Q).f n =
      Functor.OplaxMonoidal.δ F (P.X i) (Q.X j) ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) i j n h := by
  let := CondensedRing.internalScalarMonoidal a T
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans (extension a T)) (.up ℤ) P Q i j n h

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
