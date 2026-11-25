/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Shift compatibility of normalized inverse-image coefficient comparisons
Source: Stacks Project, Tags 0D6D and 07A6
(blueprint: lem-pur-coefficient-pullback-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

private theorem shift_of_dense_computation
    {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (G L : B ⥤ E)
    [G.CommShift ℤ] [L.CommShift ℤ] (F : A ⥤ E) [F.CommShift ℤ]
    (α : Q ⋙ L ⟶ F) [NatTrans.CommShift α ℤ] (t : G ⟶ L)
    [NatTrans.CommShift (whiskerLeft Q t ≫ α) ℤ]
    (dense : ∀ Y : B, ∃ (X : A) (_e : Q.obj X ≅ Y), IsIso (α.app X)) :
    NatTrans.CommShift t ℤ := by
  constructor
  intro n
  let s : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    (G.commShiftIso n).hom ≫ whiskerRight t (shiftFunctor E n)
  let u : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    whiskerLeft (shiftFunctor B n) t ≫ (L.commShiftIso n).hom
  have good (X : A) [IsIso (α.app X)] : s.app (Q.obj X) = u.app (Q.obj X) := by
    apply (cancel_mono ((shiftFunctor E n).mapIso (asIso (α.app X))).hom).1
    change s.app (Q.obj X) ≫ (α.app X)⟦n⟧' =
      u.app (Q.obj X) ≫ (α.app X)⟦n⟧'
    apply (cancel_epi (G.mapIso ((Q.commShiftIso n).app X)).hom).1
    change G.map ((Q.commShiftIso n).hom.app X) ≫ s.app (Q.obj X) ≫
      (α.app X)⟦n⟧' = G.map ((Q.commShiftIso n).hom.app X) ≫ u.app (Q.obj X) ≫
      (α.app X)⟦n⟧'
    have ht := NatTrans.shift_app_comm (whiskerLeft Q t ≫ α) n X
    have ha := NatTrans.shift_app_comm α n X
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.map_comp,
      Functor.commShiftIso_comp_hom_app, Category.assoc] at ht ha
    rw [← ha, ← t.naturality_assoc] at ht
    simpa only [s, u, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using ht
  ext Y
  obtain ⟨X, e, hX⟩ := dense Y
  let := hX
  have h := congrArg (fun f ↦ f ≫ (L ⋙ shiftFunctor E n).map e.hom) (good X)
  rw [← s.naturality, ← u.naturality] at h
  exact (cancel_epi (((shiftFunctor B n) ⋙ G).mapIso e).hom).1 h

private theorem complexComp_commShift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)
  (e : Comparisons g nY nX)
  [scalarY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    (pX a).derived.CommShift ℤ]
  (canonicalY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pY a).counit ℤ)
  (canonicalX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pX a).counit ℤ)

include canonicalY canonicalX in
omit scalarY scalarX in
omit scalarY scalarX in
include canonicalY canonicalX

end SheafOfModules.RingedCoefficientProjection
