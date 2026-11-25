/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.SmoothPurity.BifunctorProjectionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.Derived.DerivedSingleConstantsComparison
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedTensorBraidingShift

/-! # Shift and unit coherence of the unbounded etale support projection

Source: Zheng, Six operations and Lefschetz--Verdier formula for Deligne--Mumford stacks,
Theorem 2.18(2), printed p. 12, Construction 2.26, printed p. 15; Stacks Tags 0F0G,
0B56 and 0GL1 (blueprint: lem-pur-etale-support-projection-shift-unit).

The helpers only put the existing compactification projection in coefficient-first order.
They use the canonical signed tensor symmetry, never an arbitrary comparison isomorphism.
The theorem concerns the ordinary unbounded categories and the supplied compactification.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u uA vFC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Construction

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The source `(K,L) ↦ L ⊗^L F K` in coefficient-first tensor order.
Source: Zheng Theorem 2.18(2) (blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionSource :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  rightDerivedLowerShriekOfCompactification A c ⋙ (derivedTensor A Y).flip

/-- The target `(K,L) ↦ F(f^* L ⊗^L K)` with the existing exact derived inverse image.
Source: Zheng Theorem 2.18(2) (blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionTarget :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Functor.postcompose₂.obj (rightDerivedLowerShriekOfCompactification A c)).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*[A])).obj
      (derivedTensor A X).flip)

/-- The source has the canonical first-factor cochain shift comparison.
Source: Stacks Tag 0B56, signed cochain tensor convention
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable instance supportProjectionSourceCommShift
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionSource A c).obj K).CommShift ℤ :=
  inferInstanceAs (((derivedTensor A Y).flip.obj
    ((rightDerivedLowerShriekOfCompactification A c).obj K)).CommShift ℤ)

/-- The target shift comparison is the composite of exact pullback, first-factor tensor,
and the canonical derived direct-image shift comparisons.
Source: Stacks Tags 0B56, 0GL1
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable instance supportProjectionTargetCommShift
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionTarget A c).obj K).CommShift ℤ :=
  inferInstanceAs (((L((f)^*[A]) ⋙ (derivedTensor A X).flip.obj K) ⋙
    rightDerivedLowerShriekOfCompactification A c).CommShift ℤ)

variable {FC : A → A → Type vFC} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The specified proper counit projection followed by open projection, conjugated by
signed swaps to put the coefficient first. The open inverse is the derived sheaf tensor
comparison; the final swap passes through extension by zero and proper direct image.
Source: Zheng Theorem 2.18(2), Stacks Tags 0B56, 0GL1
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionMap :
    supportProjectionSource A c ⟶ supportProjectionTarget A c :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification A c)
      (derivedTensorSymmetry A Y).inv ≫
    projectionMapOfCompactification A c ≫
    (Functor.postcompose₂.obj (rightDerivedLowerShriekOfCompactification A c)).map
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*[A])).map
        (derivedTensorSymmetry A X).hom)

/-- The canonical identification of `F(f^* C_Y ⊗^L K)` with `F K`.
Source: Zheng Theorem 2.18(2), tensor-unit normalization; Stacks Tag 0B56
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionTargetUnit
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionTarget A c).obj K).obj (𝟙_ _) ≅
      (rightDerivedLowerShriekOfCompactification A c).obj K :=
  (rightDerivedLowerShriekOfCompactification A c).mapIso
    (((derivedTensor A X).flip.obj K).mapIso (leftDerivedUpperStarUnitIso A f) ≪≫
      derivedTensorLeftUnitor A X K)

/-- The target unit arrow of the support projection.
Source: Zheng Theorem 2.18(2) (blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionUnitA
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionTarget A c).obj K).obj
      (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A))) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj K :=
  (supportProjectionTargetUnit A c K).hom

/-- The source unit arrow of the support projection.
Source: Zheng Theorem 2.18(2) (blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportProjectionUnitB
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionSource A c).obj K).obj
      (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A))) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj K :=
  (derivedTensorLeftUnitor A Y
    ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom

/-- The actual map, its canonical integer-shift square (in both directions), and
its identity component at the coefficient unit, using the explicitly fixed unitors.
Source: Zheng Theorem 2.18(2), Stacks Tags 0B56 and 0GL1
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
abbrev SupportProjectionCoherent
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c) : Prop :=
  BifunctorProjectionCoherent (sT := supportProjectionSourceCommShift A c)
    (sU := supportProjectionTargetCommShift A c)
    e (supportProjectionMap A c) _
    (fun K ↦ (rightDerivedLowerShriekOfCompactification A c).obj K)
    (supportProjectionUnitA A c)
    (supportProjectionUnitB A c)

private theorem supportProjectionCoherent_iff
    (e : supportProjectionSource A c ≅ supportProjectionTarget A c) :
    SupportProjectionCoherent A c e ↔
      BifunctorProjectionCoherent (sT := supportProjectionSourceCommShift A c)
        (sU := supportProjectionTargetCommShift A c)
        e (supportProjectionMap A c) _
        (fun K ↦ (rightDerivedLowerShriekOfCompactification A c).obj K)
        (supportProjectionUnitA A c)
        (supportProjectionUnitB A c) := Iff.rfl

end Construction

section Constants

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

/-- The canonical unit identification for termwise constants: the exact-functor/single
comparison followed by the constant-sheaf and derived unit identifications.
Source: Zheng Construction 2.26
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
noncomputable def supportConstantUnitIso (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology A).mapDerivedCategory.obj
      ((_root_.DerivedCategory.singleFunctor A 0).obj (𝟙_ A)) ≅
        𝟙_ (DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  ((constantSheaf T.smallEtaleTopology A).mapDerivedCategorySingleFunctor 0).app (𝟙_ A) ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (constantSheaf T.smallEtaleTopology A)).symm ≪≫
    singleFunctorObjUnitIso A T

/-- Shift and unit normalization of a fixed constant-pullback comparison, using only
canonical exact-functor shifts and the explicit unit identifications above.
Source: Zheng Construction 2.26
(blueprint: lem-pur-etale-support-projection-shift-unit). -/
def SupportConstantPullbackCoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : (constantSheaf Y.smallEtaleTopology A).mapDerivedCategory ⋙ L((f)^*[A]) ≅
      (constantSheaf X.smallEtaleTopology A).mapDerivedCategory) : Prop :=
  NatTrans.CommShift e.hom ℤ ∧ NatTrans.CommShift e.inv ℤ ∧
    (e.hom.app ((_root_.DerivedCategory.singleFunctor A 0).obj (𝟙_ A)) ≫
      (supportConstantUnitIso A X).hom =
        L((f)^*[A]).map (supportConstantUnitIso A Y).hom ≫
          (leftDerivedUpperStarUnitIso A f).hom)

end Constants

noncomputable section UnitProof

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

private theorem supportProjection_isIso_of_proper (c : Compactification f)
    [IsIso (rightDerivedLowerStarProjectionMap A c.g)] :
    IsIso (supportProjectionMap A c) := by
  have (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
      (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
      IsIso (((projectionMapOfCompactification A c).app K).app L) := by
    rw [projectionMapOfCompactification_app_app]
    infer_instance
  have (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      IsIso ((projectionMapOfCompactification A c).app K) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (projectionMapOfCompactification A c) := NatIso.isIso_of_isIso_app _
  dsimp only [supportProjectionMap]
  infer_instance

private theorem supportProjectionMap_app (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (supportProjectionMap A c).app K =
      (derivedTensorSymmetry A Y).inv.app
        ((rightDerivedLowerShriekOfCompactification A c).obj K) ≫
      (projectionMapOfCompactification A c).app K ≫
      Functor.whiskerRight
        (Functor.whiskerLeft L((f)^*[A]) ((derivedTensorSymmetry A X).hom.app K))
        (rightDerivedLowerShriekOfCompactification A c) := rfl

omit [UpperStarPreservesFlat A] in
private theorem supportSymmetry_shift (Z : Scheme.{u})
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    NatTrans.CommShift ((derivedTensorSymmetry A Z).hom.app K) ℤ := by
  exact @_root_.DerivedCategory.canonicalTensorSymmetry_commShift _ _ _ _ _
    (Etale.sheafMonoidalCategory A Z) _ (Etale.sheafBraidedCategory A Z)
    (Etale.sheafMonoidalClosed A Z) _ K

omit [UpperStarPreservesFlat A] in
private theorem supportSymmetryInv_shift (Z : Scheme.{u})
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    NatTrans.CommShift ((derivedTensorSymmetry A Z).inv.app K) ℤ := by
  have : NatTrans.CommShift ((derivedTensorSymmetry A Z).app K).hom ℤ :=
    supportSymmetry_shift A Z K
  exact NatTrans.CommShift.of_iso_inv ((derivedTensorSymmetry A Z).app K) ℤ

omit [UpperStarPreservesFlat A] in
private theorem supportSwappedTarget_shift (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift
      (Functor.whiskerRight
        (Functor.whiskerLeft L((f)^*[A]) ((derivedTensorSymmetry A X).hom.app K))
        (rightDerivedLowerShriekOfCompactification A c)) ℤ := by
  have := supportSymmetry_shift A X K
  infer_instance

private theorem supportProjection_shift (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift ((supportProjectionMap A c).app K) ℤ := by
  let : ((derivedTensorRightDerivedLowerShriek A c).obj K).CommShift ℤ :=
    inferInstanceAs (((derivedTensor A Y).obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K)).CommShift ℤ)
  let : ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj K).CommShift ℤ :=
    inferInstanceAs (((L((f)^*[A]) ⋙ (derivedTensor A X).obj K) ⋙
      rightDerivedLowerShriekOfCompactification A c).CommShift ℤ)
  have := supportSymmetryInv_shift A Y
    ((rightDerivedLowerShriekOfCompactification A c).obj K)
  have := supportSwappedTarget_shift A c K
  have := commShift_projectionMapOfCompactification_app A c K
  change NatTrans.CommShift (F₁ := (derivedTensor A Y).flip.obj
      ((rightDerivedLowerShriekOfCompactification A c).obj K))
    (F₂ := (L((f)^*[A]) ⋙ (derivedTensor A X).flip.obj K) ⋙
      rightDerivedLowerShriekOfCompactification A c)
    ((supportProjectionMap A c).app K) ℤ
  rw [supportProjectionMap_app]
  exact NatTrans.CommShift.comp
    ((derivedTensorSymmetry A Y).inv.app
      ((rightDerivedLowerShriekOfCompactification A c).obj K))
    ((projectionMapOfCompactification A c).app K ≫
      Functor.whiskerRight
        (Functor.whiskerLeft L((f)^*[A]) ((derivedTensorSymmetry A X).hom.app K))
        (rightDerivedLowerShriekOfCompactification A c)) ℤ

private theorem canonicalSymmetry_rightUnit
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasDerivedCategory.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (K : DerivedCategory B) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry B).hom.app K).app (𝟙_ _) ≫
      (λ_ K).hom = (ρ_ K).hom := by
  let := _root_.DerivedCategory.braidedCategory' B
  exact braiding_leftUnitor K

private theorem canonicalSymmetry_invUnit
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasDerivedCategory.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (K : DerivedCategory B) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry B).inv.app K).app (𝟙_ _) ≫
      (ρ_ K).hom = (λ_ K).hom := by
  let := _root_.DerivedCategory.braidedCategory' B
  apply (cancel_epi (β_ K (𝟙_ _)).hom).1
  exact (Iso.hom_inv_id_assoc (β_ K (𝟙_ _)) _).trans
    (braiding_leftUnitor K).symm

omit [UpperStarPreservesFlat A] in
private theorem supportSymmetry_rightUnit (Z : Scheme.{u})
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    ((derivedTensorSymmetry A Z).hom.app K).app (𝟙_ _) ≫
      (derivedTensorLeftUnitor A Z K).hom = (derivedTensorRightUnitor A Z K).hom := by
  exact @canonicalSymmetry_rightUnit _ _ _ _ _
    (Etale.sheafMonoidalCategory A Z) _ (Etale.sheafBraidedCategory A Z)
    (Etale.sheafMonoidalClosed A Z) _ K

omit [UpperStarPreservesFlat A] in
private theorem supportSymmetry_invUnit (Z : Scheme.{u})
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    ((derivedTensorSymmetry A Z).inv.app K).app (𝟙_ _) ≫
      (derivedTensorRightUnitor A Z K).hom = (derivedTensorLeftUnitor A Z K).hom := by
  exact @canonicalSymmetry_invUnit _ _ _ _ _
    (Etale.sheafMonoidalCategory A Z) _ (Etale.sheafBraidedCategory A Z)
    (Etale.sheafMonoidalClosed A Z) _ K

private theorem supportProjectionMap_app_app (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((supportProjectionMap A c).app K).app L =
      ((derivedTensorSymmetry A Y).inv.app
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).app L ≫
      ((projectionMapOfCompactification A c).app K).app L ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensorSymmetry A X).hom.app K).app (L((f)^*[A]).obj L)) := rfl

omit [UpperStarPreservesFlat A] in
private theorem supportProjectionTargetUnit_hom (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (supportProjectionTargetUnit A c K).hom =
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).flip.obj K).map (leftDerivedUpperStarUnitIso A f).hom ≫
          (derivedTensorLeftUnitor A X K).hom) := rfl

private theorem compactificationProjection_app_eq (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L =
      (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap
        (leftDerivedUpperStarTensorComparison A c.g) D((c.i)_!open[A])
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (fun L ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app L) K L := rfl

private theorem compactificationProjection_rightUnit (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app (𝟙_ _) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).obj K).map (leftDerivedUpperStarUnitIso A f).hom ≫
          (derivedTensorRightUnitor A X K).hom) =
      (derivedTensorRightUnitor A Y
        ((rightDerivedLowerShriekOfCompactification A c).obj K)).hom := by
  rw [compactificationProjection_app_eq]
  exact compactificationProjectionMap_rightUnitality A c K

private theorem supportProjection_unit (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((supportProjectionMap A c).app K).app (𝟙_ _) ≫
      supportProjectionUnitA A c K = supportProjectionUnitB A c K := by
  unfold supportProjectionUnitA supportProjectionUnitB
  rw [supportProjectionMap_app_app, supportProjectionTargetUnit_hom]
  have hn := ((derivedTensorSymmetry A X).hom.app K).naturality
    (leftDerivedUpperStarUnitIso A f).hom
  simp only [Functor.flip_obj_map] at hn ⊢
  simp only [Category.assoc]
  rw [← Functor.map_comp,
    ← Category.assoc (((derivedTensorSymmetry A X).hom.app K).app _), ← hn,
    Category.assoc, supportSymmetry_rightUnit A X K]
  rw [compactificationProjection_rightUnit A c K,
    supportSymmetry_invUnit A Y ((rightDerivedLowerShriekOfCompactification A c).obj K)]

omit [UpperStarPreservesFlat A] in
private theorem supportProjection_coherent_map (c : Compactification f)
    (σ : supportProjectionSource A c ⟶ supportProjectionTarget A c) [IsIso σ]
    (hs : ∀ K : DerivedCategory (Sheaf X.smallEtaleTopology A),
      NatTrans.CommShift (σ.app K) ℤ)
    (hu : ∀ K : DerivedCategory (Sheaf X.smallEtaleTopology A),
      (σ.app K).app (𝟙_ _) ≫ supportProjectionUnitA A c K =
        supportProjectionUnitB A c K) :
    ∃ e : supportProjectionSource A c ≅ supportProjectionTarget A c,
      BifunctorProjectionCoherent (sT := supportProjectionSourceCommShift A c)
        (sU := supportProjectionTargetCommShift A c)
        e σ _
        (fun K ↦ (rightDerivedLowerShriekOfCompactification A c).obj K)
        (supportProjectionUnitA A c)
        (supportProjectionUnitB A c) := by
  exact bifunctorIsoCoherence (sT := supportProjectionSourceCommShift A c)
    (sU := supportProjectionTargetCommShift A c)
    (supportProjectionSource A c) (supportProjectionTarget A c)
    σ _
    (fun K ↦ (rightDerivedLowerShriekOfCompactification A c).obj K)
    (supportProjectionUnitA A c)
    (supportProjectionUnitB A c)
    hs hu

private theorem supportProjection_coherent (c : Compactification f)
    [IsIso (supportProjectionMap A c)] :
    ∃ e : supportProjectionSource A c ≅ supportProjectionTarget A c,
      SupportProjectionCoherent A c e := by
  obtain ⟨e, he⟩ := supportProjection_coherent_map A c (supportProjectionMap A c)
    (supportProjection_shift A c) (supportProjection_unit A c)
  exact ⟨e, (supportProjectionCoherent_iff A c e).mpr he⟩

end UnitProof

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private theorem supportProjection_isIso (C : Type (u + 1)) [CommRing C] [Finite C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    IsIso (supportProjectionMap (ModuleCat.{u + 1} C) c) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper C isAddTorsion_of_finite c.g
  exact supportProjection_isIso_of_proper (ModuleCat.{u + 1} C) c

private theorem constantPullback_shift (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (constantFunctorCompLeftDerivedUpperStarIso C f).hom ℤ := by
  dsimp only [constantFunctorCompLeftDerivedUpperStarIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

private theorem constantAdj_unit_at_terminal
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A]
    (T : Scheme.{u}) {U : T.Etale} (hU : IsTerminal U) :
    (constantSheafAdj T.smallEtaleTopology A hU).unit.app (𝟙_ A) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf T.smallEtaleTopology A)).app
        (Opposite.op U) := by
  simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
  rw [Adjunction.homEquiv_unit]
  have : Functor.OplaxMonoidal.η (presheafToSheaf T.smallEtaleTopology A) = 𝟙 _ := rfl
  simp [this]
  rfl

private theorem constantPullbackAdj_unit
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((((constantSheafAdj Y.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
      (upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents (fun _ => Iso.refl _))).leftAdjointUniq
      (constantSheafAdj X.smallEtaleTopology A (isTerminalOverPullbackObjMkId f))).hom.app
        (𝟙_ A) = Functor.OplaxMonoidal.η (f)^*[A] := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  let a := (((constantSheafAdj Y.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
      (upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (NatIso.ofComponents (fun _ => Iso.refl _)))
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
    ((a.leftAdjointUniq (constantSheafAdj X.smallEtaleTopology _
      (isTerminalOverPullbackObjMkId f))).hom.app _) = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
  erw [Equiv.trans_apply, upperStarLowerStarAdjunction_homEquiv_η]
  simp only [Adjunction.homEquiv_unit, constantAdj_unit_at_terminal]
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) A
    Y.smallEtaleTopology X.smallEtaleTopology
    (Opposite.op (Scheme.Etale.mk (𝟙 Y)))).symm

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private theorem constantPullback_unit (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheafCompUpperStarIso C f).hom.app (𝟙_ (ModuleCat.{u + 1} C)) =
      Functor.OplaxMonoidal.η (f)^*[ModuleCat.{u + 1} C] :=
  constantPullbackAdj_unit (ModuleCat.{u + 1} C) f

private theorem supportConstantUnitIso_hom
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] (T : Scheme.{u}) :
    (supportConstantUnitIso A T).hom =
      ((constantSheaf T.smallEtaleTopology A).mapDerivedCategorySingleFunctor 0).hom.app
        (𝟙_ A) ≫ (singleFunctorObjUnitIso A T).hom := by
  have hη : Functor.OplaxMonoidal.η (constantSheaf T.smallEtaleTopology A) = 𝟙 _ := by
    change (presheafToSheaf T.smallEtaleTopology A).map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp
  simp only [supportConstantUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Functor.Monoidal.εIso_inv, hη,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

private theorem iso_transport_unit
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {a b : D} {x y : E} (e : a ≅ b) (i : x ≅ y)
    (q : F.obj a ⟶ x) (r : F.obj b ⟶ y)
    (h : F.map e.inv ≫ q = r ≫ i.inv) :
    q ≫ i.hom = F.map e.hom ≫ r := by
  rw [← cancel_epi (F.map e.inv), ← Category.assoc, h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

section ConstantUnitProof

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem constantPullback_derived_unit_of_unit
    (e : constantSheaf Y.smallEtaleTopology A ⋙ (f)^*[A] ≅
      constantSheaf X.smallEtaleTopology A)
    (he : e.hom.app (𝟙_ A) = Functor.OplaxMonoidal.η (f)^*[A]) :
    (Functor.isoWhiskerLeft (constantSheaf Y.smallEtaleTopology A).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory A f) ≪≫
      (Functor.mapDerivedCategoryCompIso (constantSheaf Y.smallEtaleTopology A)
        (f)^*[A]) ≪≫ Functor.mapDerivedCategoryNatIso e).hom.app
          ((_root_.DerivedCategory.singleFunctor A 0).obj (𝟙_ A)) ≫
      (supportConstantUnitIso A X).hom =
    L((f)^*[A]).map (supportConstantUnitIso A Y).hom ≫
      (leftDerivedUpperStarUnitIso A f).hom := by
  have hc := Functor.derived_single_constants_comparison
    (constantSheaf Y.smallEtaleTopology A)
    (f)^*[A]
    (constantSheaf X.smallEtaleTopology A)
    e (𝟙_ _)
  simp only [Iso.trans_hom, NatTrans.comp_app] at hc
  simp only [Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    supportConstantUnitIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  erw [← (leftDerivedUpperStarIsoMapDerivedCategory A f).hom.naturality_assoc]
  congr 1
  have hu' := iso_transport_unit L((f)^*[A])
    (singleFunctorObjUnitIso A Y) (singleFunctorObjUnitIso A X)
    (leftDerivedUpperStarSingleConstantSheafIso A f (𝟙_ A)).hom
    (leftDerivedUpperStarUnitIso A f).hom
    (leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp A f)
  simpa only [leftDerivedUpperStarSingleConstantSheafIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, he,
    upperStarConstantSheafIso_hom_app_tensorUnit, Category.assoc] using hu'

end ConstantUnitProof

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private theorem constantPullback_derived_unit (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantFunctorCompLeftDerivedUpperStarIso C f).hom.app
        ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj (𝟙_ _)) ≫
      (supportConstantUnitIso (ModuleCat.{u + 1} C) X).hom =
      L((f)^*[ModuleCat.{u + 1} C]).map
        (supportConstantUnitIso (ModuleCat.{u + 1} C) Y).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} C) f).hom :=
  constantPullback_derived_unit_of_unit (ModuleCat.{u + 1} C) f
    (constantSheafCompUpperStarIso C f) (constantPullback_unit C f)

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- The specified projection is a natural isomorphism, commuting with every coefficient
shift and equal to the identity at the unit. The same is true after restriction to all
constant derived coefficients, for both the map and its inverse. Pullback of constant
complexes is the existing canonical comparison, with its shift and unit normalization.
Source: Zheng Theorem 2.18(2), printed p. 12, Construction 2.26, printed p. 15;
Stacks Tags 0F0G, 0B56, 0GL1
(blueprint: lem-pur-etale-support-projection-shift-unit).

Proof plan:
1. Apply proposition-proper-direct-image-constructible-complexes--9 to the proper part c.g, E = j_!
K and unbounded L. A ring killed
   by a power of ell is torsion, including the zero ring. Conjugate the proper counit
   projection of definition-projection-formula-map--1 by lem-kun-tensor-sym.
2. Apply lem-pur-etale-open-derived-tensor to M = r^* L. Its inverse projection is the
   derived sheaf extension-by-zero tensor map. Compose with the proper map and with
   lem-kun-derived-pullback-composition-monoidal. All comparisons are derived natural
   transformations, hence independent of resolutions and natural in both variables.
3. lem-weil-pbc-ringed-projection-mate-exact supplies the proper shift/unit square;
   situation-conventions identifies exact and ringed pullback, and
   lem-weil-pbc-derived-adjunction-shift identifies the right-derived shift comparison.
   Iterate the shift square forwards and backwards. For degrees p,q and shift n,
   the signs from the second-factor shift and the swap multiply as
   (-1)^(n*p) * (-1)^(p*(q-n)) = (-1)^(p*q), by proposition-open-direct-image-preserves-finite.
4. On K-flat coefficient models the coefficient-first open tensor map is degreewise
   and has no extra sign. Reindexing commutes with this map in every summand of the
   direct-sum total, including unbounded totals. At the unit it is scalar action,
   the left unitor of lem-kun-tensor-unit.
5. Paste the proper/open shift squares and use the pullback composition unit equation
   of lem-kun-derived-pullback-composition-monoidal. This gives exactly the canonical
   source/target comparisons and the identity component at C_Y.
6. By lem-weil-pbc-finite-type-constant-exact, constants descend termwise to D(C-Mod).
   Apply lem-kun-pullback-constant degreewise; it commutes with differential signs and
   reindexing and at C[0] is the coefficient-ring identification. Substitute constant
   L in the preceding identities. Inverting the shift square and the unit identity
   gives the same properties for the inverse projection.
-/
theorem etaleSupportProjectionShiftUnit
    (k : Type u) [Field k] [IsAlgClosed k] (p ell : ℕ) [CharP k p]
    (_hp : 0 < p) (_hell : ell.Prime) (_hne : ell ≠ p)
    (C : Type (u + 1)) [CommRing C] [Finite C]
    (_hC : ∃ N : ℕ, (ell ^ N : C) = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    ∃ e : supportProjectionSource (ModuleCat.{u + 1} C) c ≅
        supportProjectionTarget (ModuleCat.{u + 1} C) c,
      SupportProjectionCoherent (ModuleCat.{u + 1} C) c e ∧
      (∀ K : DerivedCategoryModule C X,
        NatTrans.CommShift (Functor.whiskerLeft (constantFunctor C Y) (e.hom.app K)) ℤ ∧
        NatTrans.CommShift (Functor.whiskerLeft (constantFunctor C Y) (e.inv.app K)) ℤ) ∧
      SupportConstantPullbackCoherent (ModuleCat.{u + 1} C) f
        (constantFunctorCompLeftDerivedUpperStarIso C f) := by
  have := supportProjection_isIso C c
  obtain ⟨e, he⟩ := supportProjection_coherent (ModuleCat.{u + 1} C) c
  refine ⟨e, he, ?_, ?_⟩
  · intro K
    have := (he.2 K).1
    have := (he.2 K).2.1
    exact ⟨inferInstance, inferInstance⟩
  · have := constantPullback_shift C f
    have : NatTrans.CommShift (constantFunctorCompLeftDerivedUpperStarIso C f).inv ℤ :=
      NatTrans.CommShift.of_iso_inv (constantFunctorCompLeftDerivedUpperStarIso C f) ℤ
    exact ⟨inferInstance, inferInstance, constantPullback_derived_unit C f⟩

end AlgebraicGeometry.Etale
