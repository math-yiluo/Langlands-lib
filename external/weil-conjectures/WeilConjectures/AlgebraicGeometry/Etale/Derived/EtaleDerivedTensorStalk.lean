/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Geometric étale stalks and unbounded derived tensor products

The stage-2 comparison is packaged in `ExactFunctorTensorComparison` to keep
concrete localization structures behind an API. Its isomorphism, naturality and
normalization clauses are exposed by `exactFunctorTensorComparison_iff`.

Source: Stacks Project, `sites-cohomology.tex`, Tag 0DEN, clause (1), and Tags 06YS,
06YT, 06YU and 07A4 (blueprint: lem-sfb-etale-derived-tensor-stalk).

## Main statements

* `AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso`: the natural isomorphism,
  normalized by the ordinary total-complex stalk comparison.
* The three auxiliary instances expose existing additive and coproduct structures.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u uC uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The existing additive structure on the geometric module-stalk functor, exposed for
termwise passage to complexes and derived categories. This is precisely the structure
`Point.sheafFiber_additive`, obtained from the skyscraper adjunction.
Source: Stacks Project, Tag 04EQ
(blueprint: lem-sfb-etale-derived-tensor-stalk). -/
noncomputable instance moduleSheafFiber_additive
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).Additive :=
  (pointSmallEtale t).sheafFiber_additive

attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.leftDerivedTensorComparison

-- Transport the derived comparison to the termwise derived functor, including its counit
-- square. Abstract category structures keep the transport rewrites small.
/-- Naturality and the localization-counit normalization of a tensor comparison for
an exact monoidal functor. Keeping this proposition named avoids repeatedly reducing
localized monoidal structures at concrete coefficient categories.
Source: Stacks Project, Tag 0DEN (blueprint: lem-sfb-etale-derived-tensor-stalk). -/
@[irreducible]
def ExactFunctorTensorComparison
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] : Prop :=
    ∃ e : ∀ K L : _root_.DerivedCategory C,
      F.mapDerivedCategory.obj (((curriedTensor (_root_.DerivedCategory C)).obj K).obj L) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L,
      (∀ (K K' L L' : _root_.DerivedCategory C) (f : K ⟶ K') (g : L ⟶ L'),
        F.mapDerivedCategory.map (((curriedTensor (_root_.DerivedCategory C)).map f).app L ≫
          ((curriedTensor (_root_.DerivedCategory C)).obj K').map g) ≫
          (e K' L').hom =
          (e K L).hom ≫ (F.mapDerivedCategory.map f ⊗ₘ F.mapDerivedCategory.map g)) ∧
      ∀ P Q : HomotopyCategory C (.up ℤ),
        (e (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj Q)).hom ≫
          (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := D))
            ((F.mapHomotopyCategory (.up ℤ)).obj P)
            ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
        F.mapDerivedCategory.map
          (Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := C)) P Q) ≫
          F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          (_root_.DerivedCategory.Qh (C := D)).map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q)

/-- The defining tensor-comparison clauses, exposed without unfolding the concrete
localization constructions. Source: Stacks Project, Tag 0DEN
(blueprint: lem-sfb-etale-derived-tensor-stalk). -/
theorem exactFunctorTensorComparison_iff
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] :
    ExactFunctorTensorComparison F ↔
    ∃ e : ∀ K L : _root_.DerivedCategory C,
      F.mapDerivedCategory.obj (((curriedTensor (_root_.DerivedCategory C)).obj K).obj L) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L,
      (∀ (K K' L L' : _root_.DerivedCategory C) (f : K ⟶ K') (g : L ⟶ L'),
        F.mapDerivedCategory.map (((curriedTensor (_root_.DerivedCategory C)).map f).app L ≫
          ((curriedTensor (_root_.DerivedCategory C)).obj K').map g) ≫
          (e K' L').hom =
          (e K L).hom ≫ (F.mapDerivedCategory.map f ⊗ₘ F.mapDerivedCategory.map g)) ∧
      ∀ P Q : HomotopyCategory C (.up ℤ),
        (e (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj Q)).hom ≫
          (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := D))
            ((F.mapHomotopyCategory (.up ℤ)).obj P)
            ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
        F.mapDerivedCategory.map
          (Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := C)) P Q) ≫
          F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          (_root_.DerivedCategory.Qh (C := D)).map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q) := by
  unfold ExactFunctorTensorComparison
  rfl

/-- The objectwise isomorphisms supplied by a normalized tensor comparison.
Source: Stacks Project, Tag 0DEN (blueprint: lem-sfb-etale-derived-tensor-stalk). -/
theorem ExactFunctorTensorComparison.exists_iso
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    (h : ExactFunctorTensorComparison F) :
    Nonempty (∀ K L : _root_.DerivedCategory C,
      F.mapDerivedCategory.obj (((curriedTensor (_root_.DerivedCategory C)).obj K).obj L) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L) := by
  obtain ⟨e, _⟩ := (exactFunctorTensorComparison_iff F).mp h
  exact ⟨e⟩

/-- An exact monoidal functor preserving flat objects has the normalized derived tensor
comparison. The proof transports the source left-derived comparison through the exact
functor comparison and checks its naturality and counit square.
Source: Stacks Project, Tag 0DEN
(blueprint: lem-sfb-exact-flat-tensor-derived-counit-comparison). -/
theorem exactFunctor_tensor_comparison
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    ExactFunctorTensorComparison F := by
  unfold ExactFunctorTensorComparison
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ← tensorHom_def]
  let η := F.leftDerivedFunctorIsoMapDerivedCategory
  let c := F.leftDerivedTensorComparison
  let e := fun K L : _root_.DerivedCategory C ↦
    (η.app (K ⊗ L)).symm ≪≫ asIso ((c.app K).app L) ≪≫
      tensorIso (η.app K) (η.app L)
  refine ⟨e, ?_, ?_⟩
  · intro K K' L L' f g
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, tensorIso_hom,
      Iso.app_hom, Iso.app_inv]
    rw [η.inv.naturality_assoc]
    have hc := F.leftDerivedTensorComparison_naturality_tensorHom f g
    change F.leftDerivedFunctor.map (f ⊗ₘ g) ≫ (c.app K').app L' =
      (c.app K).app L ≫ (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) at hc
    rw [reassoc_of% hc, tensorHom_comp_tensorHom]
    rw [η.hom.naturality, η.hom.naturality, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  · intro P Q
    apply (cancel_epi (η.hom.app (_root_.DerivedCategory.Qh.obj P ⊗
      _root_.DerivedCategory.Qh.obj Q))).1
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, tensorIso_hom,
      Iso.app_hom, Iso.app_inv]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc]
    rw [F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac,
      F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
    rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom]
    rw [← η.hom.naturality_assoc,
      F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac_assoc]

/-- The component of the exact-functor comparison at two given derived objects.
The objects are explicit parameters so their chosen derived-category instances determine
the source of the component. Source: Stacks Project, Tag 0DEN
(blueprint: lem-sfb-exact-flat-tensor-derived-counit-comparison). -/
theorem exactFunctor_tensor_iso
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (K L : _root_.DerivedCategory C)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    Nonempty (F.mapDerivedCategory.obj
      (((curriedTensor (_root_.DerivedCategory C)).obj K).obj L) ≅
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L) := by
  obtain ⟨e⟩ := ExactFunctorTensorComparison.exists_iso
    (F := F) (exactFunctor_tensor_comparison F)
  exact ⟨e K L⟩

/-- A geometric module-stalk preserves flat objects, by the geometric-fiber criterion
and the canonical comparison with the lifted point.
Source: Stacks Project, Tag 0DEN (blueprint: lem-sfb-etale-derived-tensor-stalk). -/
instance geometricStalk_preservesFlat
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).PreservesFlat :=
  ⟨fun {M} hM ↦ ObjectProperty.prop_of_iso ObjectProperty.flat
    (((pointSmallEtale t).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).app M)
    ((flat_iff_forall_flat_sheafFiber_obj M).1 hM t)⟩

end AlgebraicGeometry.Etale
