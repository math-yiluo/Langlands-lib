/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Normalization from the degree-zero quotient equation

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: new-abelian-cech-comparison-normalization)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

set_option backward.isDefEq.respectTransparency false in
/-- The resolution augmentation represents the original Ext-zero morphism.
This is the degree-zero specialization of Mathlib's `InjectiveResolution.extMk_hom`. -/
private theorem extMk_augmentation {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A B : C} (I : InjectiveResolution B) (b : A ⟶ B) :
    I.extMk (b ≫ I.ι.f 0) 1 rfl (by simp) = Abelian.Ext.mk₀ b := by
  let := HasDerivedCategory.standard C
  open CochainComplex HomComplex in
  have h : Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (b ≫ I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv)
        (zero_add (0 : ℤ)) 1 rfl (by simp [I.cochainComplex_d 0 1 0 1 rfl rfl])) =
      ShiftedHom.mk₀ 0 rfl ((singleFunctor C 0).map b ≫ I.ι') := by
    apply Cocycle.equivHomShift.injective
    ext : 1
    apply (Cochain.fromSingleEquiv (p := 0) (q := 0) (n := 0) rfl).injective
    simp [Cocycle.equivHomShift_apply, Cochain.fromSingleEquiv,
      Cochain.rightUnshift_v, ShiftedHom.mk₀, I.ι'_f_zero, singleFunctor,
      HomologicalComplex.single_map_f_self, CategoryTheory.shiftFunctorZero',
      CochainComplex.shiftFunctorZero_eq]
  ext
  rw [I.extMk_hom]
  simp only [Category.assoc]
  erw [h]
  simp [ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀,
    DerivedCategory.singleFunctorIsoCompQ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient augmentation is injective on zero cohomology: its zero component
is a product of monomorphisms followed by a coproduct inclusion, and there are no
boundaries in degree zero. -/
private theorem beta_zero_mono
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    Mono (HomologicalComplex.homologyMap (abelianCechBeta U I) 0) := by
  have hm : Mono (((TopCat.Sheaf.cechComplexFunctor U).map (I.ι.f 0)).f 0) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    funext y
    have : Mono ((I.ι.f 0).hom.app (op (⨅ l, U (y l)))) := inferInstance
    apply (AddCommGrpCat.mono_iff_injective _).mp this
    exact congr_fun h y
  have ht : Mono ((abelianCechDouble U I).ιTotal (.up ℕ) 0 0 0 (by simp)) := by
    unfold HomologicalComplex₂.ιTotal GradedObject.ιMapObj
    infer_instance
  have : Mono ((abelianCechBeta U I).f 0) := by
    dsimp only [abelianCechBeta]
    infer_instance
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Restrictions commute with the resolution augmentation on zero cohomology.
This is the degree-zero square of the two augmentations in Stacks Tag 01EQ. -/
private theorem augmentation_zero_square
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    (TopCat.Sheaf.toCechCohomologyZero U).app F ≫
        HomologicalComplex.homologyMap (abelianCechBeta U I) 0 =
      (abelianCechSections I).liftCycles ((I.ι.f 0).hom.app (op ⊤)) 1 (by simp)
          (by
            change ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)).map
              (I.ι.f 0)) ≫
              ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)).map
                (I.cocomplex.d 0 1)) = 0
            rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]) ≫
        (abelianCechSections I).homologyπ 0 ≫
        HomologicalComplex.homologyMap (abelianCechAlpha U I) 0 := by
  simp only [TopCat.Sheaf.toCechCohomologyZero, Category.assoc,
    HomologicalComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  apply (cancel_mono (((abelianCechDouble U I).total (.up ℕ)).homologyπ 0)).mpr
  apply (cancel_mono (((abelianCechDouble U I).total (.up ℕ)).iCycles 0)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i_assoc]
  change TopCat.Sheaf.toCechCochainZero U F ≫
      ((TopCat.Sheaf.cechComplexFunctor U).map (I.ι.f 0)).f 0 ≫ _ =
    (I.ι.f 0).hom.app (op ⊤) ≫
      TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X 0) ≫ _
  simp only [← Category.assoc]
  congr 1
  ext s
  funext y
  exact NatTrans.naturality_apply (I.ι.f 0).hom
    (homOfLE (le_top (a := ⨅ l, U (y l)))).op s

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero quotient equation forces the canonical normalization.

Source: Stacks Project, Tag 01EQ, the two restriction augmentations in the proof
of Lemma 20.11.2; the degree-zero gluing identification is implemented by the
source library's cechCohomologyZeroIso.
(blueprint: new-abelian-cech-comparison-normalization)

Proof: Fix an injective resolution I. For x in Čech H-zero, represent c x by a
map a from the constant integer sheaf to I-zero using I.extMk_surjective.
Evaluation at 1 gives a global section killed by d-zero, hence a section cycle z.
Apply hc to x, a and z. In degree zero the homology projections from cycles are
isomorphisms, since both complexes start in degree zero and have no boundaries.
Consequently the resulting equality in total homology is equality of the total
zero cocycles. Compose it with iCycles and project onto the (0,0) summand.
The explicit alpha and beta formulas identify the resulting equality with the
restrictions of the section represented by a being the image of x under the
resolution augmentation, on every U_i. The degree-zero Čech gluing isomorphism
and separatedness of I-zero identify that section with the augmentation of the
global section obtained by gluing x. Exactness of the augmented resolution in
degree zero factors a uniquely as b followed by I.ι.f 0, for a map b from the constant integer
sheaf to F. The
Ext-zero cocycle formula identifies I.extMk a with Ext.mk₀ b. Evaluation of b
at 1 is the section represented by functorHZeroIso applied to c x. The preceding
restriction equality and monicity of I.ι.f 0 identify this section with the
gluing of x. Cancel this isomorphism and use equality on every x to obtain the
stated equality of morphisms.

Only the degree-zero predicate is needed; no assumption on alpha in positive
degrees is used. An empty covering forces X to be empty by hcover, so gluing and
all degree-zero groups are zero. Infinite coverings use the ordinary sheaf
condition and introduce no finiteness assumption. -/
theorem abelianCechComparison_zero_normalization
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (c : (TopCat.Sheaf.cechCohomologyFunctor U 0).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) 0).obj F)
    (hc : IsAbelianCechComparison U F 0 c) :
    c = (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv.app F ≫
      (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv.app F := by
  classical
  let I := injectiveResolution F
  let e := Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop
  let r := TopCat.Sheaf.cechCohomologyZeroIso U hcover
  apply (cancel_mono (e.hom.app F)).mp
  change c ≫ e.hom.app F = (r.inv.app F ≫ e.inv.app F) ≫ e.hom.app F
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  ext x
  let b := Abelian.Ext.addEquiv₀ (c x)
  let s := ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).homEquiv _ _ b) (ULift.up 1)
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))
  have hj : E.map (I.ι.f 0) ≫ E.map (I.cocomplex.d 0 1) = 0 := by
    rw [← E.map_comp, I.ι_f_zero_comp_complex_d, E.map_zero]
  let l := (abelianCechSections I).liftCycles (E.map (I.ι.f 0)) 1 (by simp) hj
  let z := l s
  have hz : ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ (b ≫ I.ι.f 0)) (ULift.up 1) =
        (abelianCechSections I).iCycles 0 z := by
    rw [Adjunction.homEquiv_naturality_right]
    exact (ConcreteCategory.congr_hom
      ((abelianCechSections I).liftCycles_i (E.map (I.ι.f 0)) 1 (by simp) hj) s).symm
  have hb : c x = I.extMk (b ≫ I.ι.f 0) 1 rfl (by simp) := by
    rw [extMk_augmentation]
    exact (Abelian.Ext.mk₀_addEquiv₀_apply (c x)).symm
  have hc' := hc I x (b ≫ I.ι.f 0) (by simp) z hz hb
  have hsquare := ConcreteCategory.congr_hom (augmentation_zero_square U I) s
  have : Mono (HomologicalComplex.homologyMap (abelianCechBeta U I) 0) :=
    beta_zero_mono U I
  have hx : x = (TopCat.Sheaf.toCechCohomologyZero U).app F s :=
    (AddCommGrpCat.mono_iff_injective _).mp this (hc'.trans hsquare.symm)
  have hs : (e.hom.app F) (c x) = s := rfl
  change (e.hom.app F) (c x) = r.inv.app F x
  rw [hs, hx]
  change s = r.inv.app F (r.hom.app F s)
  exact (ConcreteCategory.congr_hom (r.hom_inv_id_app F) s).symm
end AlgebraicGeometry.Scheme.Modules
