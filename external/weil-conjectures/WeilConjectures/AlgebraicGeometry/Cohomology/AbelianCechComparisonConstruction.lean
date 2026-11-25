/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # The two augmentations defining an abelian Čech comparison

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: def-pc-abelian-cech-comparison-construction)

The maps below are actual restrictions and resolution augmentations. The final
predicate characterizes a comparison using Ext cocycles on every injective
resolution; it contains no connecting-map or degree-zero normalization law.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Čech cochains preserve zero coefficient morphisms.
Source: the sectionwise differential of Stacks 01EQ. -/
private theorem cech_preservesZero {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) :
    (TopCat.Sheaf.cechComplexFunctor U).PreservesZeroMorphisms := by
  constructor
  intro F G
  apply HomologicalComplex.hom_ext
  intro n
  ext s
  rfl

attribute [local instance] cech_preservesZero

/-- Resolution sections at the whole space. Source: Stacks 01EQ.
(blueprint: def-pc-abelian-cech-comparison-construction) -/
noncomputable abbrev abelianCechSections {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex

/-- The double complex, with Čech degree first. Source: Stacks 01EQ.
(blueprint: def-pc-abelian-cech-comparison-construction) -/
noncomputable def abelianCechDouble {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  HomologicalComplex₂.flip
    (((TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)

/-- The restriction augmentation from resolution sections to the total complex.
Source: Stacks 01EQ, the map alpha.
(blueprint: def-pc-abelian-cech-comparison-construction) -/
noncomputable def abelianCechAlpha {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    abelianCechSections I ⟶ (abelianCechDouble U I).total (.up ℕ) where
  f n := TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X n) ≫
    (abelianCechDouble U I).ιTotal (.up ℕ) 0 n n (by simp)
  comm' n m h := by
    have hm : n + 1 = m := h
    subst m
    let D := abelianCechDouble U I
    let r := fun n ↦ TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X n)
    change r n ≫ D.ιTotal (.up ℕ) 0 n n _ ≫ (D.total (.up ℕ)).d n (n + 1) = _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      n (n + 1) (by simp [Nat.add_comm]),
      D.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
        (n + 1) (by simp)]
    simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_zero,
      one_smul, Preadditive.comp_add]
    have hz : r n ≫ (D.d 0 1).f n = 0 :=
      TopCat.Sheaf.toCechCochainZero_d U (I.cocomplex.X n)
    rw [← Category.assoc, hz, zero_comp, zero_add]
    have hc : r n ≫ (D.X 0).d n (n + 1) =
        (abelianCechSections I).d n (n + 1) ≫ r (n + 1) := by
      ext s
      funext y
      exact NatTrans.naturality_apply (I.cocomplex.d n (n + 1)).hom
        (homOfLE (le_top (a := ⨅ l, U (y l)))).op s
    rw [← Category.assoc, hc, Category.assoc]

/-- The coefficient augmentation into the total complex.
Source: Stacks 01EQ, the map beta.
(blueprint: def-pc-abelian-cech-comparison-construction) -/
noncomputable def abelianCechBeta {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    (TopCat.Sheaf.cechComplexFunctor U).obj F ⟶
      (abelianCechDouble U I).total (.up ℕ) where
  f n := ((TopCat.Sheaf.cechComplexFunctor U).map (I.ι.f 0)).f n ≫
    (abelianCechDouble U I).ιTotal (.up ℕ) n 0 n (by simp)
  comm' n m h := by
    have hm : n + 1 = m := h
    subst m
    let T := TopCat.Sheaf.cechComplexFunctor U
    let D := abelianCechDouble U I
    change (T.map (I.ι.f 0)).f n ≫ D.ιTotal (.up ℕ) n 0 n _ ≫
      (D.total (.up ℕ)).d n (n + 1) = _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
      0 (n + 1) (by simp),
      D.d₂_eq' (.up ℕ) n (by simp : (ComplexShape.up ℕ).Rel 0 1)]
    simp only [ComplexShape.ε₁_def, one_smul]
    have hz : (T.map (I.ι.f 0)).f n ≫ (T.map (I.cocomplex.d 0 1)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, ← T.map_comp,
        I.ι_f_zero_comp_complex_d, T.map_zero]
      rfl
    have hv : (T.map (I.ι.f 0)).f n ≫ (D.X n).d 0 1 = 0 := hz
    rw [Preadditive.comp_add]
    simp only [Linear.comp_units_smul, ← Category.assoc, hv, zero_comp,
      smul_zero, add_zero]
    change ((T.map (I.ι.f 0)).f n ≫ (T.obj (I.cocomplex.X 0)).d n (n + 1)) ≫
      D.ιTotal (.up ℕ) (n + 1) 0 (n + 1) _ = _
    rw [(T.map (I.ι.f 0)).comm n (n + 1)]
    rfl


/-- A comparison is the quotient of the two augmentations on every resolution.
The Ext cocycle a corresponds to the section cycle z by the constant-sheaf
adjunction, evaluated on 1. Thus the equation uses the canonical resolution
identification, and does not quantify over arbitrary homology isomorphisms.
Source: Stacks 01EQ, alpha/beta characterization.
(blueprint: def-pc-abelian-cech-comparison-construction) -/
def IsAbelianCechComparison {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ)
    (c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F) : Prop :=
  ∀ (I : InjectiveResolution F)
    (x : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (abelianCechSections I).cycles q),
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
        (abelianCechSections I).iCycles q z →
    c x = I.extMk a (q + 1) rfl ha →
    HomologicalComplex.homologyMap (abelianCechBeta U I) q x =
      HomologicalComplex.homologyMap (abelianCechAlpha U I) q
        ((abelianCechSections I).homologyπ q z)

end AlgebraicGeometry.Scheme.Modules
