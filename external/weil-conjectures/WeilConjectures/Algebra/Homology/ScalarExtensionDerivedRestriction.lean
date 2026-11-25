/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Scalar-extension derived counits after exact restriction -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

/-- Restriction of a universal derived scalar-extension pair is universal.
Source: Stacks Project, Tags 06Y6 and 06XN, the K-flat derived-functor construction.
(blueprint: lem-pc-scalar-extension-derived-restriction).

Proof: resolve every source complex by a K-flat complex. Scalar extension inverts
quasi-isomorphisms between such complexes. Restriction is exact and therefore
preserves these quasi-isomorphisms and their images under localization. The
restricted counit is invertible on each K-flat complex, since the original
universal scalar-extension counit is invertible there. The left derivability
structure of K-flat complexes characterizes the universal pair by precisely
this condition, proving the assertion. The factorization isomorphism merely
identifies exact restriction before and after localization. The proof works for
unbounded complexes and zero rings and requires no flatness of either ring map. -/
theorem scalarExtensionDerivedRestriction
    {A D B : Type u} [CommRing A] [CommRing D] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} D)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (f : A →+* D) (s : ModuleCat.{u} D ⥤ ModuleCat.{u} B)
    [s.Additive] [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    (L ⋙ s.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε s.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((extendScalars f).mapHomotopyCategory (.up ℤ))
          s.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  classical
  open MonoidalCategory in
  have (N : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  have : (extendScalars f).PreservesKFlatQuasiIso :=
    ⟨fun hK hK' a ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat f a
      (show QuasiIso a from inferInstance) hK hK'⟩
  let : MonoidalCategory (HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) :=
    HomotopyCategory.MonoidalCategory.instMonoidalCategory _ _
  let H := (extendScalars f).mapHomotopyCategory (.up ℤ) ⋙
    s.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hd : (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)).localizerMorphismKFlat.Derives
      H := by
    intro X Y a ha
    have h := (extendScalars f).derives_kFlat a ha
    have : IsIso (DerivedCategory.Qh.map
        (((extendScalars f).mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.map a))) := by
      simpa only [Functor.comp_map] using h
    have : IsIso (s.mapDerivedCategory.map
        (DerivedCategory.Qh.map (((extendScalars f).mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.map a)))) :=
      inferInstance
    have hn := s.mapDerivedCategoryFactorsh.hom.naturality
      (((extendScalars f).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.map a))
    dsimp only [Functor.comp_map] at hn
    dsimp only [H, Functor.comp_map]
    rw [← isIso_comp_left_iff (s.mapDerivedCategoryFactorsh.hom.app _), ← hn]
    infer_instance
  apply hd.isLeftDerivedFunctor_of_isIso
  intro X
  obtain ⟨K, hK⟩ := X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff K).1 hK
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) :=
    ((extendScalars f).isLeftDerivedFunctor_iff_isIso_app_of_kFlat ε).1 hL K hk
  dsimp only [NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change IsIso (𝟙 _ ≫ s.mapDerivedCategory.map
    (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫ 𝟙 _ ≫
    s.mapDerivedCategoryFactorsh.hom.app
      (((extendScalars f).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫ 𝟙 _)
  infer_instance

end ModuleCat
