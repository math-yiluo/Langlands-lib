/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleTensor

/-! # Flatness and the constant-coefficient realization

Source: Stacks Project, Modules on Sites, Sections 03EK and 03ER.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Flatness is unchanged by extending constant scalars and the canonical ring transport.
Source: Stacks Project, Modules on Sites, Sections 03EK and 03ER, together with the
constant-scalar equivalence in Sections 093I and 03CV
(blueprint: lem-pur-etale-constant-module-flat).

Proof: for module-valued sheaves F and G, the sectionwise balanced map into the tensor
of their realizations sends x tensor y to x tensor y. Locally a section of the constant
ring sheaf is represented by a constant scalar. Consequently balancing by its sections
imposes exactly the locally constant scalar relations already satisfied by the
sheafification of the tensor over A. Sheafification's universal property gives inverse
maps between these tensors. Both composites are identities on pure tensors, and hence
on the sheafifications. These maps are natural in G. Canonical ring-isomorphism
transport also preserves this tensor comparison, by the same balanced universal
property. The realization is an equivalence, so it preserves and reflects finite limits
and finite colimits. Thus its tensor comparison identifies exactness of right tensor by
F with exactness of siteSheafTensorRight by its realization. Symmetry of the tensor
identifies left and right tensor exactness, so this is precisely ObjectProperty.flat F.
This works for the zero ring and the empty scheme: the same universal properties and
sheafification, including empty covering sieves, still apply. -/
theorem etaleConstantModule_flat_iff (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ObjectProperty.flat F ↔
      SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology) (R :=
        (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        ((etaleConstantModuleFunctor T A ⋙
          SheafOfModules.pushforward (F := 𝟭 T.Etale)
            (constantModuleHomRingIso T.smallEtaleTopology A).inv).obj F) := by
  let E := etaleSumTensorTestRealization T A
  let := etaleSumTensorTestRealization_isEquivalence T A
  obtain ⟨t⟩ := etaleConstantModule_tensorRight_comparison T A F
  let S := SheafOfModules.siteSheafTensorRight.{_, _, _, u + 1} (J := T.smallEtaleTopology)
    (A := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of A)) (E.obj F)
  have ht : E ⋙ S ≅ MonoidalCategory.tensorRight F ⋙ E := t
  have hright : ObjectProperty.flat F ↔ exactFunctor _ _ (MonoidalCategory.tensorRight F) := by
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨(exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight F).symm h, h⟩
  rw [hright]
  change exactFunctor _ _ (MonoidalCategory.tensorRight F) ↔ exactFunctor _ _ S
  constructor
  · intro h
    have := h.preservesFiniteLimits
    have := h.preservesFiniteColimits
    let e := E.asEquivalence
    let i : S ≅ e.inverse ⋙ MonoidalCategory.tensorRight F ⋙ E :=
      (Functor.leftUnitor S).symm ≪≫
        Functor.isoWhiskerRight e.counitIso.symm S ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse ht
    exact (exactFunctor _ _).prop_of_iso i.symm
      ((exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩)
  · intro h
    have := h.preservesFiniteLimits
    have := h.preservesFiniteColimits
    have : PreservesFiniteLimits (E ⋙ S) := inferInstance
    have : PreservesFiniteColimits (E ⋙ S) := inferInstance
    have : PreservesFiniteLimits (MonoidalCategory.tensorRight F ⋙ E) :=
      preservesFiniteLimits_of_natIso ht
    have : PreservesFiniteColimits (MonoidalCategory.tensorRight F ⋙ E) :=
      preservesFiniteColimits_of_natIso ht
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ E,
      preservesFiniteColimits_of_reflects_of_preserves _ E⟩

end AlgebraicGeometry.Scheme
