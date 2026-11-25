/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Tensor complexes with independent site universes

Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: def-pur-sheaf-tensor-product)

The tensor is the existing localization tensor, with no restriction equating
site object, site morphism, and coefficient universes.
-/

@[expose] public section

universe uC vC w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option autoImplicit false
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R : Sheaf J CommRingCat.{w})

private noncomputable def tensorPresheafIso
    (M N : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    M ⊗ N ≅ siteTensorPresheaf M N :=
  PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl)

private theorem tensor_W_right
    {M M' : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (hf : (J.W.inverseImage (PresheafOfModules.toPresheaf _)) f)
    (N : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    (J.W.inverseImage (PresheafOfModules.toPresheaf _)) (f ▷ N) := by
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    (R.obj ⋙ forget₂ CommRingCat RingCat))
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  -- Direct local descent avoids a change of site.
  have h := PresheafOfModules.sheafification_tensorHom_isIso f (N := N)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property
  have hi : W (siteTensorHom f N) := by
    change (J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)) (siteTensorHom f N)
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)]
    exact h
  apply (W.arrow_mk_iso_iff (Arrow.isoMk (tensorPresheafIso R M N)
    (tensorPresheafIso R M' N) (by
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl))).2 hi

/-- Tensoring preserves local equivalences on any essentially small site.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: replace the site by its small model in universe w. The tensor and
sheafification universal properties commute with this equivalence. On the
small model local tensoring preserves local equivalences, and transport back
preserves this assertion. -/
@[instance]
theorem cochainTensorLocalizationIsMonoidal :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).IsMonoidal := by
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have left (F : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat))
      {P Q : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)}
      (g : P ⟶ Q) (hg : W g) : W (F ◁ g) := by
    exact (W.arrow_mk_iso_iff
      (Arrow.isoMk (β_ P F) (β_ Q F))).1 (tensor_W_right R g hg F)
  exact
    { whiskerLeft F _ _ g hg := left F g hg
      whiskerRight f hf G := tensor_W_right R f hf G }

/-- The existing localization tensor, with independent site sizes.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable instance cochainModulesMonoidal :
    MonoidalCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  @monoidalCategory.{vC, uC, w} C _ J _ R _ _ (cochainTensorLocalizationIsMonoidal R)

/-- The existing symmetric structure of the localization tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable instance cochainModulesSymmetric :
    SymmetricCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  @symmetricCategory.{vC, uC, w} C _ J _ R _ _ (cochainTensorLocalizationIsMonoidal R)

private theorem tensorLeft_preserves_smallColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  let L := PresheafOfModules.sheafification.{w}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have : L.Monoidal := inferInstance
  have : PreservesColimitsOfSize.{w, w} (tensorLeft M.val) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w}
      (tensorLeft (show PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)
        from M.val)))
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M.val) :=
    preservesSmallestColimits_of_preservesColimits _
  let e : L.obj M.val ≅ M := (asIso adj.counit).app M
  let i : L ⋙ tensorLeft M ≅ tensorLeft M.val ⋙ L :=
    Functor.isoWhiskerLeft L ((curriedTensor _).mapIso e.symm) ≪≫
      Functor.Monoidal.commTensorLeft L M.val
  have : PreservesColimitsOfSize.{0, 0} (L ⋙ tensorLeft M) :=
    preservesColimits_of_natIso i.symm
  exact (adj.preservesColimitsOfSize_iff (tensorLeft M)).2 this

/-- The sheaf tensor is additive in each variable, independently of site sizes.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: additivity holds sectionwise on pure tensors and descends through the
additive sheafification functor; the localization tensor has those same maps. -/
@[instance]
theorem cochainModulesPreadditive :
    MonoidalPreadditive (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := by
  have left (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      (tensorLeft M).Additive := by
    have := tensorLeft_preserves_smallColimits R M
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have right (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      (tensorRight M).Additive :=
    Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

/-- Left tensoring preserves the coproducts used in unbounded total tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: bilinear maps out of a direct sum are families of bilinear maps.
The tensor universal property and sheafification adjunction identify the
coproduct comparison with this bijection, so it is invertible. -/
@[instance]
theorem cochainTensorLeftPreservesColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  exact tensorLeft_preserves_smallColimits R M

/-- Right tensoring preserves the coproducts used in unbounded total tensor.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: conjugate left tensoring by the existing symmetric braiding. -/
@[instance]
theorem cochainTensorRightPreservesColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

end SheafOfModules
