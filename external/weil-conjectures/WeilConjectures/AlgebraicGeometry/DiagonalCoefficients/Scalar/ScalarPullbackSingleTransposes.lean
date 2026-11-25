/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Transpose formulas for shifted scalar and geometric endpoints

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
  paragraph (3), final sentence (blueprint: lem-sfb-scalar-pullback-single-transposes).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local instance 100001] sheafMonoidalCategory sheafBraidedCategory
attribute [local implicit_reducible] derivedScalars
attribute [local implicit_reducible] sheafMonoidalCategory
  sheafBraidedCategory sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal SymmetricCategory.ofCurried

attribute [local irreducible] upperStarFromPoint

attribute [local instance] isCommMonObj_condensedRingObj
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem commShift_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : ∀ n, F.commShiftIso (self := s) n = F.commShiftIso (self := t) n) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact h n

private theorem adjoint_shift_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] :
    adj.leftAdjointCommShift ℤ = s := by
  apply commShift_ext
  intro n
  exact Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n)
    (adj.shift_unit_app n)

private theorem homEquiv_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {V : D ⥤ C} [F.CommShift ℤ] [V.CommShift ℤ]
    (adj : F ⊣ V) [adj.CommShift ℤ] {M : C} {N : D} (g : F.obj M ⟶ N) (n : ℤ) :
    adj.homEquiv _ _ ((F.commShiftIso n).hom.app M ≫ g⟦n⟧') ≫
        (V.commShiftIso n).hom.app N = (adj.homEquiv _ _ g)⟦n⟧' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [adj.shift_unit_app]
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]

private theorem mate_transpose
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L : C ⥤ D} {V : D ⥤ C} {L' : E ⥤ H} {V' : H ⥤ E}
    (adj : L ⊣ V) (adj' : L' ⊣ V') (F : C ⥤ E) (G : D ⥤ H)
    (b : G ⋙ V' ≅ V ⋙ F) {K : C} {B : D} {B' : H}
    (g : L.obj K ⟶ B) (d : G.obj B ⟶ B') :
    adj'.homEquiv _ _ ((Adjunction.pushHomOfComapIso adj adj' b).app K ≫
        G.map g ≫ d) =
      F.map (adj.homEquiv _ _ g) ≫ b.inv.app B ≫ V'.map d := by
  have hu := unit_mateEquiv_symm adj adj'
    (TwoSquare.mk _ _ _ _ b.inv) K
  change F.map (adj.unit.app K) ≫ b.inv.app (L.obj K) =
    adj'.unit.app (F.obj K) ≫ V'.map
      ((Adjunction.pushHomOfComapIso adj adj' b).app K) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu]
  have hn := b.inv.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private theorem shifted_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : C ⥤ D) (V : C ⥤ A) (W : D ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (b : G ⋙ W ≅ V ⋙ F) [NatTrans.CommShift b.hom ℤ]
    {N : C} {NS : A} {NT : D} {NX NY : B}
    (zS : V.obj N ⟶ NS) (tR : F.obj NS ⟶ NY)
    (tT : G.obj N ⟶ NT) (zX : W.obj NT ⟶ NX) (e : NX ⟶ NY)
    (h : b.hom.app N ≫ F.map zS ≫ tR = W.map tT ≫ zX ≫ e) (n : ℤ) :
    b.hom.app (N⟦n⟧) ≫
        F.map ((V.commShiftIso n).hom.app N ≫ zS⟦n⟧') ≫
        (F.commShiftIso n).hom.app NS ≫ tR⟦n⟧' =
      W.map ((G.commShiftIso n).hom.app N ≫ tT⟦n⟧') ≫
        (W.commShiftIso n).hom.app NT ≫ zX⟦n⟧' ≫ e⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hb := NatTrans.shift_app_comm b.hom n N
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  rw [← reassoc_of% hb]
  have hh := congrArg (fun k ↦ (shiftFunctor B n).map k) h
  simp only [Functor.map_comp] at hh
  rw [hh]
  rw [← Functor.commShiftIso_hom_naturality_assoc]

private theorem invert_square {C : Type*} [Category C] {A B D E H : C}
    (b : A ≅ B) (z : B ≅ D) (t : D ⟶ H) (u : A ⟶ E) (e : E ≅ H)
    (h : b.hom ≫ z.hom ≫ t = u ≫ e.hom) :
    z.inv ≫ b.inv ≫ u = t ≫ e.inv := by
  apply (cancel_epi z.hom).mp
  apply (cancel_epi b.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using (congrArg (fun k ↦ k ≫ e.inv) h).symm

section ExactSquare
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

private theorem exact_square_single
    (F : A ⥤ B) (G : C ⥤ D) (V : C ⥤ A) (W : D ⥤ B)
    [F.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (e : G ⋙ W ≅ V ⋙ F) (N : C) :
    ((Functor.mapDerivedCategoryCompIso G W ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso V F).symm).hom.app
          ((DerivedCategory.singleFunctor C 0).obj N)) ≫
      F.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (V.obj N) =
    W.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (W.mapDerivedCategorySingleFunctor 0).hom.app (G.obj N) ≫
      (DerivedCategory.singleFunctor B 0).map (e.hom.app N) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso G W).inv.app
    ((DerivedCategory.singleFunctor C 0).obj N))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G W N]
  simp only [Category.assoc]
end ExactSquare

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)

private theorem geometric_shift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift (F₁ := derivedUpper R f)
      (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom ℤ := by
  have hs := (CondensedRing.kflat_derived_adjunction_transport_shifts (Mon.mk R) f).2.2
  have he : derivedUpperCommShift R f =
      CondensedRing.modulePullbackDerivedCommShift R f := by
    exact adjoint_shift_eq
      (F := CondensedRing.moduleObjectDerivedPullback R f)
      (G := CondensedRing.moduleObjectDerivedPushforward R f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
  change NatTrans.CommShift (F₁ := derivedUpper R f)
    (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
    (CondensedRing.modulePullbackExactComparison R f).hom ℤ
  rw [he]
  exact (CondensedRing.module_derived_functors_exact_and_comparison_shifts R f).2.2.1

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
