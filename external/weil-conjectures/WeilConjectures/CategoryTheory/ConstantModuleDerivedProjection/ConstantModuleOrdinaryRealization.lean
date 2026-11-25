/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleDerivedComparisonData
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Ordinary constant-module realization of a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV (6), Modules on Sites, Tag 03EL,
and Cohomology on Sites, Tag 07A4
(blueprint: lem-sfb-constant-module-ordinary-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option linter.privateModule false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]

-- Cache the standard sheafification properties before the repeated section calculations.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance cachedAdd (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{max u v} := inferInstance

private instance cachedWeakComm (J : GrothendieckTopology C) :
    HasWeakSheafify J CommRingCat.{max u v} := inferInstance

private instance cachedWeakRing (J : GrothendieckTopology C) :
    HasWeakSheafify J RingCat.{max u v} := inferInstance

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance cachedWeakFixed (J : GrothendieckTopology C)
    (A : Type (max u v)) [CommRing A] : HasWeakSheafify J (ModuleCat.{max u v} A) :=
  inferInstance

private instance cachedForgetRing (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  inferInstance

attribute [local irreducible] presheafToSheaf

private def scalarValue (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (U : Cᵒᵖ) (b : B) : (ring J B).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b

private def scalarSection
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) :
    (constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1} ⟶
      (sheafCompose J (forget CommRingCat.{max u v})).obj (ring J B) :=
  (constantSheaf J (Type (max u v))).map (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget CommRingCat.{max u v})).inv.app (CommRingCat.of B)

set_option backward.isDefEq.respectTransparency false in
-- Compare the commutative-ring and ring sheafification units.
private theorem restriction_scalar (M : Modules J A) (U : Cᵒᵖ) (a : A)
    (x : M.val.obj U) :
    @SMul.smul A (((restriction J A).obj M).obj.obj U) inferInstance a x =
      scalarValue J A U a • x := by
  dsimp only [scalarValue]
  change ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
    (CommRingCat.of A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) • x = _
  congr 1
  have hf := congrArg (fun f ↦ f.app U a)
    (sheafComposeIso_hom_fac J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
  have hp := congrArg (fun f ↦ f.app U a) (toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).hom.app (CommRingCat.of A)))
  dsimp at hp
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) _ = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) z) hp.symm).trans hf

-- Keep chosen sheafification functors behind their naturality APIs.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarValue ring

-- The scalar action can be tested on the binary operation (x,y) ↦ b • x + y.
set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] CategoryTheory.sfbSheafTensorStructure
set_option backward.isDefEq.respectTransparency true

private theorem insertion_isIso (d : GeometricData J K A) (M : Modules J A) :
    IsIso (d.ringTensor.q M) := by
  obtain ⟨θ, _, hinv, _⟩ := exists_scalarExtensionRingIso.{u, v, max u v, max u v} d.scalarIso
  let U := toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring K A)) ⋙
      sheafCompose K (forget AddCommGrpCat.{max u v})
  let e := U.mapIso (eqToIso (d.object_eq M)) ≪≫ U.mapIso (θ (d.algebraic.modules.obj M))
  have h : d.ringTensor.q M = e.inv := by
    ext W x
    exact (d.ringTensor.q_one M W x).trans
      (congrArg (fun y ↦ (eqToHom (d.object_eq M).symm).val.app W y)
        (hinv (d.algebraic.modules.obj M) W x).symm)
  rw [h]
  exact ⟨⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩⟩


set_option backward.isDefEq.respectTransparency false in
private theorem fixedPure_map {M M' N N' : Fixed J A}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (x : M.obj.obj W) (y : N.obj.obj W) :
    (f ⊗ₘ g).hom.app W (fixedPure J A M N W x y) =
      fixedPure J A M' N' W (f.hom.app W x) (g.hom.app W y) := by
  let P := presheafToSheaf J (ModuleCat.{max u v} A)
  let : P.Monoidal :=
    (sfbSheafTensorStructure (A := ModuleCat.{max u v} A) J).sheafificationMonoidal
  have hc {T T' : Fixed J A} (h : T ⟶ T') :
      h ≫ (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T')).inv =
        (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T)).inv ≫
          P.map h.hom := by
    apply (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T)).eq_inv_comp.mpr
    rw [← Category.assoc]
    exact (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T')).comp_inv_eq.mpr
      ((sheafificationAdjunction J (ModuleCat A)).counit.naturality h).symm
  have hn : (f ⊗ₘ g) ≫ (sfbSheafTensor_comparison J M' N').hom =
      (sfbSheafTensor_comparison J M N).hom ≫ P.map (f.hom ⊗ₘ g.hom) := by
    dsimp only [sfbSheafTensor_comparison]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
      Functor.Monoidal.μIso_hom, Category.assoc]
    erw [← Functor.LaxMonoidal.μ_natural]
    rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    rw [hc f, hc g]
  have hi : (sfbSheafTensor_comparison J M N).inv ≫ (f ⊗ₘ g) =
      P.map (f.hom ⊗ₘ g.hom) ≫ (sfbSheafTensor_comparison J M' N').inv := by
    apply (cancel_epi (sfbSheafTensor_comparison J M N).hom).1
    apply (cancel_mono (sfbSheafTensor_comparison J M' N').hom).1
    simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using hn
  have hu := toSheafify_naturality J (f.hom ⊗ₘ g.hom)
  have he := congrArg (fun k ↦ k.hom.app W
    ((toSheafify J (M.obj ⊗ N.obj)).app W (x ⊗ₜ[A] y))) hi
  dsimp only [fixedPure]
  change (f ⊗ₘ g).hom.app W _ = _ at he
  apply he.trans
  have h := congrArg (fun k ↦ k.app W (x ⊗ₜ[A] y)) hu
  exact congrArg ((sfbSheafTensor_comparison J M' N').inv.hom.app W) h.symm

-- Transport through a monoidal equivalence, retaining an explicit tensor formula.
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] CategoryTheory.ConstantScalarRestriction.fixedMonoidal
  CategoryTheory.ConstantScalarRestriction.restrictionBraided

end CategoryTheory.ConstantModuleDerivedProjection
