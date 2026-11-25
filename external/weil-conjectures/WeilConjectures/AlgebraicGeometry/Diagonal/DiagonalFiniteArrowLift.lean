/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalResidueDerivedFactorization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite residue lifting of strict derived arrows

Source: diagonal tower system proof, step (2) and evaluation in step (4).
(blueprint: lem-sfb-diagonal-finite-arrow-lift). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
  CategoryTheory.Abelian.Ext.homEquiv CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.mapExactFunctor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary exactFunctorExtImage

/-- Residue lifting for evaluated derived-reduction arrows, with all categories
and scalar functors shared parameters. This is the displayed restriction equation,
not a choice of a residue class.
Source: diagonal tower system proof, steps (2) and (4)
(blueprint: lem-sfb-diagonal-finite-arrow-lift). -/
@[irreducible] def DiagonalFiniteArrowLifting
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    {C : Type*} [Category C] [abC : Abelian C] [hC : HasExt.{w} C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (D : DiagonalDerivedReduction ℓ L)
    (F : C ⥤ B) [Fadd : F.Additive] [Flim : PreservesFiniteLimits F]
    [Fcolim : PreservesFiniteColimits F]
    (n : ℕ) : Prop :=
  ∀ (M : A) (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (P : C) (t : H.obj (op n) ≅ F.obj P) (S : A)
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S)),
    a.hom = diagonalDerivedSingleCounit ℓ L D S →
    ∀ (Q : C) (s : (D.ordinary.E.obj S).obj (op n) ≅ F.obj Q)
      (f : Ext S M 1), ∃ e : Ext Q P 2,
      exactFunctorExtImage F e =
        (Ext.mk₀ s.inv).comp
          (((Ext.homEquiv.symm (a.inv ≫ D.T.map f.hom ≫ b.hom)).mapExactFunctor
            ((evaluation ℕᵒᵖ B).obj (op n))).comp
            (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2)

/-- The concrete compatibility formula, with its coefficient expressions shared.
This is a real proposition definition and chooses no data.
(blueprint: lem-sfb-diagonal-finite-arrow-lift). -/
@[irreducible] def diagonalFiniteArrowLiftingStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) (n : ℕ) : Prop :=
  DiagonalFiniteArrowLifting
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := diagonalFiniteToPadicColimits ℓ n W)
    ℓ (diagonalScalarExtension ℓ W) D (diagonalFiniteToPadic ℓ n W) n

private theorem lift_pure_iso
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] (X Y : DerivedCategory C₁) (i : ℤ) [Y.IsGE i] [Y.IsLE i]
    (e : F.mapDerivedCategory.obj X ≅ F.mapDerivedCategory.obj Y) :
    ∃ a : X ≅ Y, F.mapDerivedCategory.map a.hom = e.hom := by
  have : (F.mapDerivedCategory.obj Y).IsGE i := F.isGE_mapDerivedCategory_obj Y i
  have : (F.mapDerivedCategory.obj Y).IsLE i := F.isLE_mapDerivedCategory_obj Y i
  have : (F.mapDerivedCategory.obj X).IsGE i :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm i
  have : (F.mapDerivedCategory.obj X).IsLE i :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm i
  have hX := F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    (a := i) (b := i) (X := X) ⟨inferInstance, inferInstance⟩
  have : X.IsGE i := hX.1
  have : X.IsLE i := hX.2
  obtain ⟨P, ⟨p⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X i
  obtain ⟨Q, ⟨q⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y i
  let H := DerivedCategory.singleFunctor C₁ i ⋙ F.mapDerivedCategory
  let : H.Full := Functor.Full.of_iso (F.mapDerivedCategorySingleFunctor i).symm
  let : H.Faithful := Functor.Faithful.of_iso (F.mapDerivedCategorySingleFunctor i).symm
  let j := H.preimageIso (F.mapDerivedCategory.mapIso p.symm ≪≫ e ≪≫
    F.mapDerivedCategory.mapIso q)
  refine ⟨p ≪≫ (DerivedCategory.singleFunctor C₁ i).mapIso j ≪≫ q.symm, ?_⟩
  change F.mapDerivedCategory.map
    (p.hom ≫ (DerivedCategory.singleFunctor C₁ i).map (H.preimage _) ≫ q.inv) = e.hom
  simp only [Functor.map_comp]
  change F.mapDerivedCategory.map p.hom ≫ H.map (H.preimage _) ≫
    F.mapDerivedCategory.map q.inv = e.hom
  rw [H.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    ← F.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id,
    ← F.mapDerivedCategory.map_comp]
  rw [F.mapDerivedCategory.map_id, F.mapDerivedCategory.map_id,
    Category.id_comp, Category.comp_id]

private theorem finite_restriction_full (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Full := by
  have hsurj : Function.Surjective (diagonalResidueProjection.{u} ℓ n) := by
    intro x
    refine ⟨ULift.up (x.down.val : ℤ_[ℓ]), ?_⟩
    apply ULift.ext
    change PadicInt.toZModPow (n + 1) (x.down.val : ℤ_[ℓ]) = x.down
    rw [map_natCast, ZMod.natCast_zmod_val]
  let : (ModuleCat.restrictScalars.{u + 1} (diagonalResidueProjection.{u} ℓ n)).Full :=
    { map_surjective := fun {M N} g ↦ ⟨ModuleCat.ofHom
        { toFun := g
          map_add' := g.hom.map_add
          map_smul' := fun r m ↦ by
            obtain ⟨a, rfl⟩ := hsurj r
            exact g.hom.map_smul a m }, rfl⟩ }
  unfold diagonalFiniteToPadic
  infer_instance

private theorem finite_restriction_faithful (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Faithful := by
  unfold diagonalFiniteToPadic
  infer_instance

private theorem finite_lift_of_factorization
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    {C : Type*} [Category C] [abC : Abelian C] [hC : HasExt.{w} C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory B] [HasDerivedCategory C]
    (L : A ⥤ B) (D : DiagonalDerivedReduction ℓ L)
    (F : C ⥤ B) [Fadd : F.Additive] [Flim : PreservesFiniteLimits F]
    [Fcolim : PreservesFiniteColimits F]
    [F.Full] [F.Faithful] (n : ℕ)
    (R : DerivedCategory A ⥤ DerivedCategory C)
    (γ : R ⋙ F.mapDerivedCategory ≅
      D.T ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory) :
    DiagonalFiniteArrowLifting ℓ L D F n := by
  unfold DiagonalFiniteArrowLifting
  intro M H b P t S a _ha Q s f
  let V := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  let U := F.mapDerivedCategory
  let X := (DerivedCategory.singleFunctor A 0).obj S
  let Y := ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧
  let Q₀ := (DerivedCategory.singleFunctor C 0).obj Q
  let P₂ := ((DerivedCategory.singleFunctor C 0).obj P)⟦(2 : ℤ)⟧
  let src : U.obj (R.obj X) ≅ U.obj Q₀ :=
    γ.app X ≪≫ V.mapIso a ≪≫
      (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor B 0).mapIso s ≪≫
      ((F.mapDerivedCategorySingleFunctor 0).app Q).symm
  let dst : U.obj (R.obj Y) ≅ U.obj P₂ :=
    γ.app Y ≪≫ V.mapIso b ≪≫ (V.commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor (DerivedCategory B) (2 : ℤ)).mapIso
        ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor B 0).mapIso t) ≪≫
      ((U.commShiftIso (2 : ℤ)).app _ ≪≫
        (shiftFunctor (DerivedCategory B) (2 : ℤ)).mapIso
          ((F.mapDerivedCategorySingleFunctor 0).app P)).symm
  obtain ⟨α, hα⟩ := lift_pure_iso F (R.obj X) Q₀ 0 src
  have : P₂.IsGE (-2) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by decide)
  have : P₂.IsLE (-2) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)
  obtain ⟨β, hβ⟩ := lift_pure_iso F (R.obj Y) P₂ (-2) dst
  let e : Ext Q P 2 := Ext.homEquiv.symm (α.inv ≫ R.map f.hom ≫ β.hom)
  refine ⟨e, ?_⟩
  have hα' : U.map α.inv = src.inv := by
    have h : U.mapIso α = src := Iso.ext hα
    exact congrArg Iso.inv h
  apply Ext.homEquiv.injective
  simp only [exactFunctorExtImage, Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [e, Ext.hom, Equiv.apply_symm_apply, ShiftedHom.map, Functor.map_comp,
    Category.assoc]
  rw [hα', hβ]
  simp only [src, dst, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  dsimp only [U, V]
  have hn : F.mapDerivedCategory.map (R.map (Ext.homEquiv f)) ≫ γ.hom.app Y =
      γ.hom.app X ≫ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
        (D.T.map (Ext.homEquiv f)) := γ.hom.naturality (Ext.homEquiv f)
  rw [reassoc_of% hn]
  simp only [Functor.comp_obj, Nat.cast_ofNat, Iso.inv_hom_id_app_assoc,
    ← (shiftFunctor (DerivedCategory B) (2 : ℤ)).map_comp,
    Iso.inv_hom_id_app, (shiftFunctor (DerivedCategory B) (2 : ℤ)).map_id,
    Category.comp_id]

/-- Evaluation of a strict derived-reduction arrow lifts to residue coefficients.

Source: diagonal tower system proof, steps (2) and (4), before the Kummer
identification (blueprint: lem-sfb-diagonal-finite-arrow-lift).

Proof: form ordinary extension to the residue ring by taking the quotient of
scalar extension by the positive prime power, in residue-module sheaves. Its
restriction to p-adic modules identifies with evaluation of D.ordinary by the
cokernel universal property. Derive this comparison on common flat-term K-flat
resolutions. Exact restriction retains the underlying complexes and reflects
quasi-isomorphisms, and evaluation of strict systems preserves these derived
comparisons. Consequently evaluation of D.T factors through derived extension
to the residue ring. The canonical source counit a and s identify its source
with Q in degree zero. The isomorphism b followed by evaluation and t identifies
its target after restriction with P[2]. Restriction reflects concentration of
cohomology; the fully faithful restriction on the hearts lifts this last
identification to residue modules. Apply the residue derived functor to f,
conjugate by these two identifications, and use the Ext/Hom equivalence to get
e. Its restriction is the displayed arrow by naturality of the common
resolution comparison. This uses no Kummer sequence, roots identification,
adjunction generator, or sign convention. Arbitrary isomorphisms s,t are
allowed because restriction is full on the hearts; no assertion of fullness
on all derived morphisms is used. -/
theorem diagonal_finite_arrow_lift (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) (n : ℕ) :
    diagonalFiniteArrowLiftingStatement ℓ W D n := by
  let := HasDerivedCategory.standard (DiagonalMod ℓ W)
  let := HasDerivedCategory.standard
    (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
  let := finite_restriction_full ℓ n W
  let := finite_restriction_faithful ℓ n W
  obtain ⟨R, ⟨γ⟩⟩ := diagonal_residue_derived_factorization ℓ W n D
  unfold diagonalFiniteArrowLiftingStatement
  exact finite_lift_of_factorization
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := diagonalFiniteToPadicColimits ℓ n W)
    ℓ (diagonalScalarExtension ℓ W) D (diagonalFiniteToPadic ℓ n W) n R γ

end AlgebraicGeometry.ProEtale
