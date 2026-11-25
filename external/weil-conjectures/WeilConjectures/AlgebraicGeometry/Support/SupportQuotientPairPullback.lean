/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Support.SupportQuotientFlat
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf

import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Functorial pullback of constant support quotients

Source: Stacks Project, Tag 03Q1, especially (1) and (3), and the ordinary comparison
in the final paragraph of blueprint `lem-pur-kunneth-supported.proof.md`
(blueprint: lem-pur-support-quotient-pair-pullback).

The quotients and quotient maps are exactly those of `SupportQuotientFlat`. The
fixed-scalar presentation is the same presentation used by that dependency: its canonical
realization identifies it with ordinary modules over the constant ring sheaf. The helper
structures only bundle the schemes, closed immersions and factorization hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The input closed pair, including precisely the quasi-compact-complement hypothesis.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPair where
  T : Scheme.{u}
  C : Scheme.{u}
  a : C ⟶ T
  closed : IsClosedImmersion a
  qc : QuasiCompact a.openComplement.ι

attribute [instance] SupportQuotientPair.closed SupportQuotientPair.qc

/-- A scheme morphism carrying the source closed subscheme into the target, with its
scheme-theoretic factorization, rather than merely an inclusion of underlying sets.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPairMap (P Q : SupportQuotientPair.{u}) where
  f : P.T ⟶ Q.T
  s : P.C ⟶ Q.C
  w : s ≫ Q.a = P.a ≫ f

/-- Identity input pair map.
Source: the identity clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.id (P : SupportQuotientPair.{u}) : SupportQuotientPairMap P P :=
  ⟨𝟙 P.T, 𝟙 P.C, (Category.id_comp P.a).trans (Category.comp_id P.a).symm⟩

/-- Composite input pair map, using the composite of the supplied factorizations.
Source: the composition clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.comp {P Q R : SupportQuotientPair.{u}}
    (g : SupportQuotientPairMap P Q) (f : SupportQuotientPairMap Q R) :
    SupportQuotientPairMap P R :=
  ⟨g.f ≫ f.f, g.s ≫ f.s,
    (Category.assoc g.s f.s R.a).trans
      ((congrArg (fun k ↦ g.s ≫ k) f.w).trans
        ((Category.assoc g.s Q.a f.f).symm.trans
          ((congrArg (fun k ↦ k ≫ f.f) g.w).trans (Category.assoc P.a g.f f.f))))⟩

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ConstantSections

universe v₁ v₂ v₃ u₁ u₂ u₃ w

variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D : Type w} [Category D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃)
  [HasWeakSheafify J₁ D] [HasWeakSheafify J₂ D] [HasWeakSheafify J₃ D]

private def constantDirect (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂] (N : D) :
    (constantSheaf J₁ D).obj N ⟶
      (F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N) :=
  ((sheafificationAdjunction J₁ D).homEquiv _ _).symm
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))

private theorem constantDirect_unit (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    (N : D) (W : C₁ᵒᵖ) :
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₂ F N).hom.app W =
        (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)).app (F.op.obj W) := by
  have h := ((sheafificationAdjunction J₁ D).homEquiv
    ((Functor.const C₁ᵒᵖ).obj N)
    ((F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N))).apply_symm_apply
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app W) h

private def constantInverse (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    {L : Sheaf J₁ D ⥤ Sheaf J₂ D}
    (a : L ⊣ F.sheafPushforwardContinuous D J₁ J₂) (N : D) :
    L.obj ((constantSheaf J₁ D).obj N) ⟶ (constantSheaf J₂ D).obj N :=
  (a.homEquiv _ _).symm (constantDirect J₁ J₂ F N)

private theorem constantDirect_comp
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃] [H.IsContinuous J₁ J₃]
    (e : F ⋙ G ≅ H) (N : D) :
    constantDirect J₁ J₂ F N ≫
      (F.sheafPushforwardContinuous D J₁ J₂).map (constantDirect J₂ J₃ G N) ≫
        (Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).hom.app
          ((constantSheaf J₃ D).obj N) = constantDirect J₁ J₃ H N := by
  apply ((sheafificationAdjunction J₁ D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  change (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₂ F N).hom.app W ≫
      (constantDirect J₂ J₃ G N).hom.app (F.op.obj W) ≫
      (((Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).hom.app
        ((constantSheaf J₃ D).obj N)).hom.app W) =
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₃ H N).hom.app W
  rw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  rw [← Category.assoc, ← Category.assoc, constantDirect_unit]
  change ((toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)).app (F.op.obj W) ≫
      (constantDirect J₂ J₃ G N).hom.app (F.op.obj W)) ≫
      ((constantSheaf J₃ D).obj N).obj.map (e.inv.app W.unop).op = _
  rw [constantDirect_unit, constantDirect_unit]
  have hn := (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).naturality
    (e.inv.app W.unop).op
  change (𝟙 N) ≫
      (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).app (H.op.obj W) =
    (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).app (G.op.obj (F.op.obj W)) ≫
      (sheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).map (e.inv.app W.unop).op at hn
  exact hn.symm.trans (Category.id_comp _)

private theorem homEquiv_mate
    {E E' : Type*} [Category E] [Category E']
    {L L' : E ⥤ E'} {R R' : E' ⥤ E} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {X : E} {Y : E'} (t : L'.obj X ⟶ Y) :
    a.homEquiv X Y
        (((conjugateIsoEquiv a b).symm d.symm).inv.app X ≫ t) =
      b.homEquiv X Y t ≫ d.hom.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app X ≫
      R.map (((conjugateEquiv b a).symm d.hom).app X)) ≫ R.map t = _
  rw [← unit_conjugateEquiv_symm b a d.hom X, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

private theorem constantInverse_composite_adjunct
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃]
    {L₁ : Sheaf J₁ D ⥤ Sheaf J₂ D} {L₂ : Sheaf J₂ D ⥤ Sheaf J₃ D}
    (a₁ : L₁ ⊣ F.sheafPushforwardContinuous D J₁ J₂)
    (a₂ : L₂ ⊣ G.sheafPushforwardContinuous D J₂ J₃) (N : D) :
    (a₁.comp a₂).homEquiv _ _
        (L₂.map (constantInverse J₁ J₂ F a₁ N) ≫ constantInverse J₂ J₃ G a₂ N) =
      constantDirect J₁ J₂ F N ≫
        (F.sheafPushforwardContinuous D J₁ J₂).map (constantDirect J₂ J₃ G N) := by
  rw [Adjunction.comp_homEquiv]
  change a₁.homEquiv _ _ (a₂.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  unfold constantInverse
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]

private theorem constantInverse_comp
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃] [H.IsContinuous J₁ J₃]
    {L₁ : Sheaf J₁ D ⥤ Sheaf J₂ D} {L₂ : Sheaf J₂ D ⥤ Sheaf J₃ D}
    {L₃ : Sheaf J₁ D ⥤ Sheaf J₃ D}
    (a₁ : L₁ ⊣ F.sheafPushforwardContinuous D J₁ J₂)
    (a₂ : L₂ ⊣ G.sheafPushforwardContinuous D J₂ J₃)
    (a₃ : L₃ ⊣ H.sheafPushforwardContinuous D J₁ J₃)
    (e : F ⋙ G ≅ H) (N : D) :
    constantInverse J₁ J₃ H a₃ N =
      ((conjugateIsoEquiv a₃ (a₁.comp a₂)).symm
        (Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).symm).inv.app
          ((constantSheaf J₁ D).obj N) ≫
        L₂.map (constantInverse J₁ J₂ F a₁ N) ≫ constantInverse J₂ J₃ G a₂ N := by
  apply (a₃.homEquiv _ _).injective
  unfold constantInverse
  rw [Equiv.apply_symm_apply, homEquiv_mate, Adjunction.comp_homEquiv]
  change _ = a₁.homEquiv _ _ (a₂.homEquiv _ _ _) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simpa only [Category.assoc] using (constantDirect_comp J₁ J₂ J₃ F G H e N).symm

end ConstantSections

section Construction

private abbrev Coeff (A : Type u) [CommRing A] :=
  ModuleCat.{u + 1} (ULift.{u + 1, u} A)

variable (A : Type u) [CommRing A]

variable [Finite A]

end Construction

end AlgebraicGeometry.Scheme
