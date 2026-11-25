/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Pullback of augmented extended Cech objects

Source: Stacks Project, algebraization.tex, Tags 099E, 099F and 0A0G;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-augmented-cech-object-pullback).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Derived inverse image transports the augmented Cech object and the coefficient ring.
This statement concerns objects and augmentation arrows; it has no tensor action variable.

Source: Stacks Project, algebraization.tex, Tags 099E, 099F and 0A0G;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-augmented-cech-object-pullback).

Proof: construct the ordinary module pullback as algebraic inverse image followed by
extension of scalars. Its K-flat derived functor is left adjoint to Rf; uniqueness
identifies it with L. The ordinary pullback of the rank-one free module is RX, and
this module is flat, so its degree-zero complex gives j. Work on the finite-generator
cover of Y and its inverse-image cover, refined by source representables. On these
sheaf slices, localization inverse-image coherence gives the unit-preserving
comparison between the localization of RY at each generator and the localization of
RX at its structural image. Scalar extension preserves this localization formula.
Consequently it preserves the two-term augmented localization complex and each
finite tensor total, including its differential signs. Those complexes are K-flat
and compute derived pullback. Their localization maps commute with restrictions and
refinement, so their augmented comparisons descend on canonical global Cech models.
The local description of any supplied model identifies its internal-Hom completion
functor with that canonical model, preserving its unit, by uniqueness of the completion
reflection. Taking their left adjoints identifies the augmented tensor actions, and
evaluating at the coefficient ring identifies the augmented objects. Compose these
identifications with the canonical-model comparison to obtain d and its augmentation
square. All identifications commute with the canonical localization comparison, so
transport between the independently supplied derived-category universes preserves j,
d, and that square. For a zero ideal the objects and augmentations are the coefficient
rings and identities. For the unit ideal they are zero derived objects, and the
augmentation square is the unique zero square. -/
theorem ringed_augmentedCech_object_pullback
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX] [IX.IsFiniteType]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX)
    (a : L ⊣ Rf)
 :
    ∃ j : L.obj (DerivedCategory.Q.{wY}.obj (ringedSiteRingComplex RY)) ≅
        DerivedCategory.Q.{wX}.obj (ringedSiteRingComplex RX),
      ∀ (KX : ringedSiteComplex RX) (εX : KX ⟶ ringedSiteRingComplex RX),
        HasLocalExtendedCechDescription.{u, wX} RX IX ιX KX εX →
      ∀ (KY : ringedSiteComplex RY) (εY : KY ⟶ ringedSiteRingComplex RY),
        HasLocalExtendedCechDescription.{u, wY} RY IY ιY KY εY →
      ∃ d : L.obj (DerivedCategory.Q.{wY}.obj KY) ≅ DerivedCategory.Q.{wX}.obj KX,
        d.hom ≫ DerivedCategory.Q.{wX}.map εX =
          L.map (DerivedCategory.Q.{wY}.map εY) ≫ j.hom := by
  sorry

end CategoryTheory
