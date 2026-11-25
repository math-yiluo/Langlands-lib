/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.Tactic.IrreducibleDef

/-!
# Injective module sheaves on a ringed-site hypercover

Source: Stacks Project, Hypercoverings, Tags 01GE and 01GW, ringed-module analogue
(auxiliary; not a blueprint node).

The conclusion is the explicit exact-sequence formulation of the augmentation
quasi-isomorphism. The matching hypothesis is expressed by local lifting of every
compatible lower-simplex tuple over the augmentation object. This includes degree zero.
-/

@[expose] public section

universe u v r

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.RingedHypercover

set_option backward.isDefEq.respectTransparency false in
private noncomputable irreducible_def freeObjMap.{u', v', r'}
    {C : Type u'} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{r'})
    (A : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X) (ULift.{max u' v' r'} (unop X ⟶ A) →₀ R.obj X) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (ULift.{max u' v' r'} (unop Y ⟶ A) →₀ R.obj Y)) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ULift.{max u' v' r'} (unop Y ⟶ A) →₀ R.obj Y)))
    (Finsupp.linearCombination (R.obj X)
      (M := (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (ULift.{max u' v' r'} (unop Y ⟶ A) →₀ R.obj Y)))
      (fun a ↦ Finsupp.single (ULift.up (f.unop ≫ a.down)) 1))

@[simp]
private lemma freeObjMap_single.{u', v', r'}
    {C : Type u'} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{r'}) (A : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : ULift.{max u' v' r'} (unop X ⟶ A)) (b : R.obj X) :
    (freeObjMap.{u', v', r'} R A f) (Finsupp.single a b) =
      Finsupp.single (ULift.up (f.unop ≫ a.down)) (R.map f b) := by
  rw [freeObjMap_def.{u', v', r'}]
  change (Finsupp.linearCombination (R.obj X)
    (M := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ULift.{max u' v' r'} (unop Y ⟶ A) →₀ R.obj Y)))
    (fun a ↦ Finsupp.single (ULift.up (f.unop ≫ a.down)) 1)) (Finsupp.single a b) = _
  rw [Finsupp.linearCombination_single]
  change (R.map f b) • (Finsupp.single _ 1 : _ →₀ R.obj Y) = _
  simp

variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{r})

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeObj (A : C) : PresheafOfModules.{max u v r} R where
  obj X := ModuleCat.of (R.obj X) (ULift.{max u v r} (unop X ⟶ A) →₀ R.obj X)
  map f := freeObjMap.{u, v, r} R A f
  map_id X := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (freeObjMap.{u, v, r} R A (𝟙 X)) (Finsupp.single a 1) = Finsupp.single a 1
    simp only [freeObjMap_single.{u, v, r}, map_one, unop_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (freeObjMap.{u, v, r} R A (f ≫ g)) (Finsupp.single a 1) =
      (freeObjMap.{u, v, r} R A g) ((freeObjMap.{u, v, r} R A f) (Finsupp.single a 1))
    simp only [freeObjMap_single.{u, v, r}, map_one, unop_comp, Category.assoc]

@[simp]
private lemma freeObj_map_single (A : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : ULift.{max u v r} (unop X ⟶ A)) (b : R.obj X) :
    (freeObj.{u, v, r} R A).map f (Finsupp.single a b) =
      Finsupp.single (ULift.up (f.unop ≫ a.down)) (R.map f b) := by
  exact freeObjMap_single.{u, v, r} R A f a b

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeMap {A B : C} (f : A ⟶ B) : freeObj.{u, v, r} R A ⟶ freeObj R B where
  app X := ModuleCat.ofHom (Finsupp.lmapDomain _ _ (fun a ↦ ULift.up (a.down ≫ f)))
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (Finsupp.lmapDomain (R.obj Y) (R.obj Y)
      (fun a ↦ ULift.up (a.down ≫ f))) ((freeObj R A).map g (Finsupp.single a 1)) =
      (freeObj R B).map g ((Finsupp.lmapDomain (R.obj X) (R.obj X)
        (fun a ↦ ULift.up (a.down ≫ f))) (Finsupp.single a 1))
    simp [Finsupp.lmapDomain_apply, Category.assoc]

@[simp]
private lemma freeMap_single {A B : C} (f : A ⟶ B) (X : Cᵒᵖ)
    (a : ULift.{max u v r} (unop X ⟶ A)) (b : R.obj X) :
    (freeMap.{u, v, r} R f).app X (Finsupp.single a b) =
      Finsupp.single (ULift.up (a.down ≫ f)) b := by
  exact Finsupp.mapDomain_single

private noncomputable def freeFunctor : C ⥤ PresheafOfModules.{max u v r} R where
  obj := freeObj R
  map := freeMap R
  map_id A := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (freeMap R (𝟙 A)).app X (Finsupp.single a 1) = Finsupp.single a 1
    simp
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (freeMap R (f ≫ g)).app X (Finsupp.single a 1) =
      (freeMap R g).app X ((freeMap R f).app X (Finsupp.single a 1))
    simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeDesc (A : C) (M : PresheafOfModules.{max u v r} R)
    (s : M.obj (op A)) : freeObj R A ⟶ M where
  app X := ModuleCat.ofHom
    (Finsupp.linearCombination (R.obj X)
      (fun a : ULift.{max u v r} (unop X ⟶ A) ↦ M.map a.down.op s))
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (Finsupp.linearCombination (R.obj Y)
      (fun a : ULift.{max u v r} (unop Y ⟶ A) ↦ M.map a.down.op s))
      ((freeObj R A).map f (Finsupp.single a 1)) =
      M.map f ((Finsupp.linearCombination (R.obj X)
      (fun a : ULift.{max u v r} (unop X ⟶ A) ↦ M.map a.down.op s))
        (Finsupp.single a 1))
    simp only [freeObj_map_single, map_one, Finsupp.linearCombination_single, one_smul]
    rw [op_comp, M.map_comp_apply, Quiver.Hom.op_unop]

@[simp]
private lemma freeDesc_single (A : C) (M : PresheafOfModules.{max u v r} R)
    (s : M.obj (op A)) (X : Cᵒᵖ)
    (a : ULift.{max u v r} (unop X ⟶ A)) (b : R.obj X) :
    (freeDesc R A M s).app X (Finsupp.single a b) = b • M.map a.down.op s :=
  Finsupp.linearCombination_single _ _ _

private noncomputable def freeEquiv (A : C) (M : PresheafOfModules.{max u v r} R) :
    (freeObj R A ⟶ M) ≃+ M.obj (op A) where
  toFun f := f.app (op A) (Finsupp.single (ULift.up (𝟙 A)) 1)
  invFun := freeDesc R A M
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (freeDesc R A M _).app X (Finsupp.single a 1) = f.app X (Finsupp.single a 1)
    rw [freeDesc_single, one_smul]
    have h := PresheafOfModules.naturality_apply f a.down.op (Finsupp.single (ULift.up (𝟙 A)) 1)
    rw [freeObj_map_single] at h
    simpa using h.symm
  right_inv s := by
    change (freeDesc R A M s).app (op A) (Finsupp.single (ULift.up (𝟙 A)) 1) = s
    rw [freeDesc_single, one_smul]
    simp
  map_add' f g := rfl

@[simp]
private lemma freeEquiv_precomp {A B : C} (M : PresheafOfModules.{max u v r} R)
    (f : A ⟶ B) (g : freeObj R B ⟶ M) :
    freeEquiv R A M (freeMap R f ≫ g) = M.map f.op (freeEquiv R B M g) := by
  change g.app _ ((freeMap R f).app _ (Finsupp.single (ULift.up (𝟙 A)) 1)) = _
  rw [freeMap_single]
  have h := PresheafOfModules.naturality_apply g f.op
    (Finsupp.single (ULift.up (𝟙 B)) 1)
  rw [freeObj_map_single] at h
  change _ = M.map f.op (g.app (op B) (Finsupp.single (ULift.up (𝟙 B)) 1))
  simpa only [Quiver.Hom.unop_op, Category.comp_id, Category.id_comp, map_one] using h

/-- A presheaf section lies locally in the image of a module morphism. -/
private def LocallyInRange (J : GrothendieckTopology C)
    {P Q : PresheafOfModules.{max u v r} R} (f : P ⟶ Q) (X : C) (x : Q.obj (op X)) : Prop :=
  ∃ K : Sieve X, K ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), K g →
    ∃ y : P.obj (op Y), f.app (op Y) y = Q.map g.op x

private lemma locallyInRange_zero (J : GrothendieckTopology C)
    {P Q : PresheafOfModules.{max u v r} R} (f : P ⟶ Q) (X : C) :
    LocallyInRange R J f X 0 := by
  exact ⟨⊤, J.top_mem X, fun Y g _ ↦ ⟨0, by simp⟩⟩

private lemma locallyInRange_add (J : GrothendieckTopology C)
    {P Q : PresheafOfModules.{max u v r} R} (f : P ⟶ Q) (X : C)
    {x y : Q.obj (op X)} (hx : LocallyInRange R J f X x)
    (hy : LocallyInRange R J f X y) : LocallyInRange R J f X (x + y) := by
  obtain ⟨K, hK, hx⟩ := hx
  obtain ⟨L, hL, hy⟩ := hy
  refine ⟨K ⊓ L, J.intersection_covering hK hL, fun Y g hg ↦ ?_⟩
  obtain ⟨a, ha⟩ := hx Y g hg.1
  obtain ⟨b, hb⟩ := hy Y g hg.2
  exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

/-- The alternating free presheaf boundary, before sheafification. -/
private noncomputable def presheafBoundary (U : SimplicialObject C) (n : ℕ) :
    (freeFunctor.{u, v, r} R).obj (U _⦋n + 1⦌) ⟶ (freeFunctor R).obj (U _⦋n⦌) :=
  AlgebraicTopology.AlternatingFaceMapComplex.objD (U ⋙ freeFunctor R) n

set_option backward.isDefEq.respectTransparency false in
private lemma presheafBoundary_zero_single (U : SimplicialObject C) (X : C)
    (a : X ⟶ U _⦋1⦌) (b : R.obj (op X)) :
    (presheafBoundary.{u, v, r} R U 0).app (op X) (Finsupp.single (ULift.up a) b) =
      Finsupp.single (ULift.up (a ≫ U.δ 0)) b -
        Finsupp.single (ULift.up (a ≫ U.δ 1)) b := by
  change ((∑ j : Fin 2, (-1 : ℤ) ^ j.val • freeMap R (U.δ j)).app (op X)) _ = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  rw [PresheafOfModules.add_app, PresheafOfModules.neg_app]
  change (((freeMap R (U.δ 0)).app (op X) +
    -(freeMap R (U.δ 1)).app (op X)).hom) (Finsupp.single (ULift.up a) b) = _
  rw [ModuleCat.hom_add, ModuleCat.hom_neg]
  rw [LinearMap.add_apply, LinearMap.neg_apply]
  rw [sub_eq_add_neg]
  exact congrArg₂ (fun x y ↦ x + -y)
    (freeMap_single R (U.δ 0) (op X) (ULift.up a) b)
    (freeMap_single R (U.δ 1) (op X) (ULift.up a) b)

private noncomputable def presheafShortComplex (U : SimplicialObject C) (n : ℕ) :
    ShortComplex (PresheafOfModules.{max u v r} R) :=
  .mk (presheafBoundary R U (n + 1)) (presheafBoundary R U n)
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (U ⋙ freeFunctor R) n)

set_option backward.isDefEq.respectTransparency false in
private lemma presheafBoundary_single (U : SimplicialObject C) (n : ℕ) (X : C)
    (a : X ⟶ U _⦋n + 1⦌) (b : R.obj (op X)) :
    (presheafBoundary.{u, v, r} R U n).app (op X) (Finsupp.single (ULift.up a) b) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.single (ULift.up (a ≫ U.δ i)) b := by
  let E := PresheafOfModules.evaluation.{max u v r} R (op X)
  let : E.Additive := by infer_instance
  change E.map (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • freeMap R (U.δ i)) _ = _
  rw [Functor.map_sum]
  simp only [Functor.map_zsmul]
  change ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (freeMap R (U.δ i)).app (op X)).hom) (Finsupp.single (ULift.up a) b) = _
  rw [ModuleCat.hom_sum]
  simp only [LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x ↦ (-1 : ℤ) ^ i.val • x) (freeMap_single R (U.δ i) (op X) _ b)

private lemma presheafBoundary_augmentation (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) :
    presheafBoundary.{u, v, r} R U 0 ≫ freeMap R (e.app (op ⦋0⦌)) = 0 := by
  let F := freeFunctor.{u, v, r} R
  have h (j : Fin 2) : U.δ j ≫ e.app (op ⦋0⦌) = e.app (op ⦋1⦌) := by
    exact (e.naturality (SimplexCategory.δ j).op).trans (Category.comp_id _)
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.map (U.δ j)) ≫ F.map _ = 0
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ← F.map_comp, h]
  simp [Fin.sum_univ_two]

private noncomputable def presheafAugmentationShortComplex (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) :
    ShortComplex (PresheafOfModules.{max u v r} R) :=
  .mk (presheafBoundary R U 0) (freeMap R (e.app (op ⦋0⦌)))
    (presheafBoundary_augmentation R W U e)

variable (J : GrothendieckTopology C) (S : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]



private noncomputable def freeSheafFunctor : C ⥤ SheafOfModules.{max u v r} S :=
  freeFunctor S.obj ⋙ PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)

private noncomputable def sectionEquiv (A : C) (I : SheafOfModules.{max u v r} S) :
    ((freeSheafFunctor.{u, v, r} J S).obj A ⟶ I) ≃+ I.val.obj (op A) := by
  let : (PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).left_adjoint_additive
  exact ((PresheafOfModules.sheafificationAdjunction.{max u v r}
    (𝟙 S.obj)).homAddEquiv _ I).trans (freeEquiv S.obj A _)

private lemma sectionEquiv_precomp {A B : C} (f : A ⟶ B)
    (I : SheafOfModules.{max u v r} S) (g : (freeSheafFunctor J S).obj B ⟶ I) :
    sectionEquiv J S A I ((freeSheafFunctor J S).map f ≫ g) =
      I.val.map f.op (sectionEquiv J S B I g) := by
  change freeEquiv S.obj A _
    ((PresheafOfModules.sheafificationAdjunction.{max u v r} (𝟙 S.obj)).homEquiv _ I
      ((PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)).map (freeMap S.obj f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeEquiv_precomp S.obj _ f _

private noncomputable def boundary (U : SimplicialObject C) (n : ℕ) :
    (freeSheafFunctor.{u, v, r} J S).obj (U _⦋n + 1⦌) ⟶
      (freeSheafFunctor J S).obj (U _⦋n⦌) :=
  AlgebraicTopology.AlternatingFaceMapComplex.objD (U ⋙ freeSheafFunctor J S) n

private lemma sectionEquiv_boundary (U : SimplicialObject C) (n : ℕ)
    (I : SheafOfModules.{max u v r} S)
    (g : (freeSheafFunctor J S).obj (U _⦋n⦌) ⟶ I) :
    sectionEquiv J S (U _⦋n + 1⦌) I (boundary J S U n ≫ g) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        I.val.map (U.δ j).op (sectionEquiv J S (U _⦋n⦌) I g) := by
  dsimp only [boundary, AlgebraicTopology.AlternatingFaceMapComplex.objD]
  rw [CategoryTheory.Preadditive.sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CategoryTheory.Preadditive.zsmul_comp, map_zsmul]
  congr 1
  exact sectionEquiv_precomp J S (U.δ j) I g

private noncomputable def shortComplex (U : SimplicialObject C) (n : ℕ) :
    ShortComplex (SheafOfModules.{max u v r} S) :=
  .mk (boundary J S U (n + 1)) (boundary J S U n)
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared
      (U ⋙ freeSheafFunctor J S) n)

private lemma boundary_augmentation (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) :
    boundary J S U 0 ≫ (freeSheafFunctor J S).map (e.app (op ⦋0⦌)) = 0 := by
  let F := freeSheafFunctor.{u, v, r} J S
  have h (j : Fin 2) : U.δ j ≫ e.app (op ⦋0⦌) = e.app (op ⦋1⦌) := by
    exact (e.naturality (SimplexCategory.δ j).op).trans (Category.comp_id _)
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.map (U.δ j)) ≫ F.map _ = 0
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ← F.map_comp, h]
  simp [Fin.sum_univ_two]

private noncomputable def augmentationShortComplex (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) :
    ShortComplex (SheafOfModules.{max u v r} S) :=
  .mk (boundary J S U 0) ((freeSheafFunctor J S).map (e.app (op ⦋0⦌)))
    (boundary_augmentation J S W U e)

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
private lemma sections_isSheaf (I : SheafOfModules.{max u v r} S) :
    Presieve.IsSheaf J (I.val.presheaf ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type J _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J I.val.presheaf (forget _) I.isSheaf)

private lemma augmentation_epi_of_local_lifts (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (h : ∃ Q : Sieve W, Q ∈ J W ∧ ∀ (V : C) (f : V ⟶ W), Q f →
      ∃ t : V ⟶ U _⦋0⦌, t ≫ e.app (op ⦋0⦌) = f) :
    Epi ((freeSheafFunctor.{u, v, r} J S).map (e.app (op ⦋0⦌))) := by
  obtain ⟨Q, hQ, ht⟩ := h
  constructor
  intro I g k hgk
  apply (sectionEquiv J S W I).injective
  apply ((sections_isSheaf J S I).isSeparated Q hQ).ext
  intro V f hf
  obtain ⟨t, htf⟩ := ht V f hf
  have heq := congrArg (sectionEquiv J S (U _⦋0⦌) I) hgk
  rw [sectionEquiv_precomp, sectionEquiv_precomp] at heq
  change I.val.map f.op _ = I.val.map f.op _
  rw [← htf, op_comp, I.val.map_comp_apply, I.val.map_comp_apply]
  exact congrArg (fun x ↦ I.val.map t.op x) heq

private lemma sheafification_epi_of_local_lifts
    {P Q : PresheafOfModules.{max u v r} S.obj} (f : P ⟶ Q)
    (h : ∀ (X : C) (x : Q.obj (op X)), ∃ K : Sieve X, K ∈ J X ∧
      ∀ (Y : C) (g : Y ⟶ X), K g → ∃ y : P.obj (op Y),
        f.app (op Y) y = Q.map g.op x) :
    Epi ((PresheafOfModules.sheafification (𝟙 S.obj)).map f) := by
  constructor
  intro I a b hab
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v r} (𝟙 S.obj)
  apply (adj.homEquiv Q I).injective
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨K, hK, hy⟩ := h X.unop x
  apply ((sections_isSheaf J S I).isSeparated K hK).ext
  intro Y g hg
  obtain ⟨y, hfy⟩ := hy Y g hg
  have heq := congrArg (adj.homEquiv P I) hab
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left] at heq
  have heq' := congrArg (fun t : P ⟶ _ ↦ t.app (op Y) y) heq
  have ha := PresheafOfModules.naturality_apply (adj.homEquiv Q I a) g.op x
  have hb := PresheafOfModules.naturality_apply (adj.homEquiv Q I b) g.op x
  change _ = I.val.map g.op _ at ha hb
  change I.val.map g.op _ = I.val.map g.op _
  rw [← ha, ← hb, ← hfy]
  exact heq'

private lemma sheafification_exact_of_local_boundaries
    (T : ShortComplex (PresheafOfModules.{max u v r} S.obj))
    (h : ∀ (X : C) (x : T.X₂.obj (op X)), T.g.app (op X) x = 0 →
      ∃ K : Sieve X, K ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), K g →
        ∃ y : T.X₁.obj (op Y), T.f.app (op Y) y = T.X₂.map g.op x) :
    (T.map (PresheafOfModules.sheafification (𝟙 S.obj))).Exact := by
  let L := PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)
  let : L.Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).left_adjoint_additive
  let p := Limits.kernel.lift T.g T.f T.zero
  have hp : Epi (L.map p) := by
    apply sheafification_epi_of_local_lifts J S p
    intro X x
    have hx : T.g.app (op X) ((Limits.kernel.ι T.g).app (op X) x) = 0 := by
      have hh := congrArg (fun t : Limits.kernel T.g ⟶ T.X₃ ↦ t.app (op X) x)
        (Limits.kernel.condition T.g)
      exact hh
    obtain ⟨K, hK, hy⟩ := h X ((Limits.kernel.ι T.g).app (op X) x) hx
    refine ⟨K, hK, fun Y g hg ↦ ?_⟩
    obtain ⟨y, hfy⟩ := hy Y g hg
    refine ⟨y, ?_⟩
    apply PresheafOfModules.injective_of_mono (Limits.kernel.ι T.g) (op Y)
    have hpι := congrArg (fun t : T.X₁ ⟶ T.X₂ ↦ t.app (op Y) y)
      (Limits.kernel.lift_ι T.g T.f T.zero)
    change (Limits.kernel.ι T.g).app (op Y) (p.app (op Y) y) = _ at hpι
    rw [hpι, hfy]
    exact (PresheafOfModules.naturality_apply (Limits.kernel.ι T.g) g.op x).symm
  apply (T.map L).exact_iff_epi_kernel_lift.mpr
  have heq : Limits.kernel.lift (L.map T.g) (L.map T.f) (by simp [← L.map_comp]) =
      L.map p ≫ Limits.kernelComparison T.g L := by
    apply (cancel_mono (Limits.kernel.ι (L.map T.g))).mp
    simp [p]
  change Epi (Limits.kernel.lift (L.map T.g) (L.map T.f) _)
  rw [heq]
  infer_instance

private lemma sheafification_presheafBoundary (U : SimplicialObject C) (n : ℕ) :
    (PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)).map
      (presheafBoundary S.obj U n) = boundary J S U n := by
  let : (PresheafOfModules.sheafification.{max u v r} (𝟙 S.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).left_adjoint_additive
  dsimp only [presheafBoundary, boundary, AlgebraicTopology.AlternatingFaceMapComplex.objD]
  rw [Functor.map_sum]
  simp only [Functor.map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma augmentation_exact_of_local_boundaries (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (h : ∀ (X : C) (x : (freeObj.{u, v, r} S.obj (U _⦋0⦌)).obj (op X)),
      (freeMap S.obj (e.app (op ⦋0⦌))).app (op X) x = 0 →
        LocallyInRange S.obj J (presheafBoundary S.obj U 0) X x) :
    (augmentationShortComplex J S W U e).Exact := by
  have hh := sheafification_exact_of_local_boundaries J S
    (presheafAugmentationShortComplex S.obj W U e) h
  let E : (presheafAugmentationShortComplex S.obj W U e).map
      (PresheafOfModules.sheafification (𝟙 S.obj)) ≅
      augmentationShortComplex J S W U e :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        dsimp only [presheafAugmentationShortComplex, augmentationShortComplex, ShortComplex.map]
        simpa only [freeSheafFunctor, Functor.comp_obj, Iso.refl_hom,
          Category.id_comp, Category.comp_id] using
          (sheafification_presheafBoundary J S U 0).symm)
      (by simp; rfl)
  exact ShortComplex.exact_of_iso E hh

set_option backward.isDefEq.respectTransparency false in
private lemma positive_exact_of_local_boundaries (U : SimplicialObject C) (n : ℕ)
    (h : ∀ (X : C) (x : (freeObj.{u, v, r} S.obj (U _⦋n + 1⦌)).obj (op X)),
      (presheafBoundary S.obj U n).app (op X) x = 0 →
        LocallyInRange S.obj J (presheafBoundary S.obj U (n + 1)) X x) :
    (shortComplex J S U n).Exact := by
  have hh := sheafification_exact_of_local_boundaries J S
    (presheafShortComplex S.obj U n) h
  let E : (presheafShortComplex S.obj U n).map
      (PresheafOfModules.sheafification (𝟙 S.obj)) ≅ shortComplex J S U n :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        exact (Category.id_comp _).trans
          ((sheafification_presheafBoundary J S U (n + 1)).symm.trans
            (Category.comp_id _).symm))
      (by
        dsimp only [presheafShortComplex, shortComplex, ShortComplex.map]
        simpa only [freeSheafFunctor, Functor.comp_obj, Iso.refl_hom,
          Category.id_comp, Category.comp_id] using
          (sheafification_presheafBoundary J S U n).symm)
  exact ShortComplex.exact_of_iso E hh


end CategoryTheory.RingedHypercover

namespace CategoryTheory.RingedHypercover
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (R : Cᵒᵖ ⥤ RingCat.{r})

set_option backward.isDefEq.respectTransparency false in
private lemma augmentation_kernel_locally_boundary (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) (hcover : HasLocalLifts J W U e)
    (T : C) (z : (freeObj.{u, v, r} R (U _⦋0⦌)).obj (op T))
    (hz : (freeMap R (e.app (op ⦋0⦌))).app (op T) z = 0) :
    LocallyInRange R J (presheafBoundary R U 0) T z := by
  classical
  by_cases hz0 : z = 0
  · rw [hz0]
    exact locallyInRange_zero R J _ T
  let A := ULift.{max u v r} (T ⟶ U _⦋0⦌)
  let B := ULift.{max u v r} (T ⟶ W)
  let f : A → B := fun a ↦ ULift.up (a.down ≫ e.app (op ⦋0⦌))
  have hne : z.support.Nonempty := Finsupp.support_nonempty_iff.mpr hz0
  let : Nonempty A := ⟨hne.choose⟩
  let g : A → A := fun a ↦ Function.invFun f (f a)
  have hgf (a : A) : (g a).down ≫ e.app (op ⦋0⦌) = a.down ≫ e.app (op ⦋0⦌) := by
    exact congrArg ULift.down (Function.invFun_eq (f := f) ⟨a, rfl⟩)
  have hlocal (a : A) (b : R.obj (op T)) :
      LocallyInRange R J (presheafBoundary R U 0) T
        (Finsupp.single a b - Finsupp.single (g a) b) := by
    obtain ⟨K, hK, ht⟩ := local_edge J W U e hcover T a.down (g a).down (hgf a).symm
    refine ⟨K, hK, fun V k hk ↦ ?_⟩
    obtain ⟨t, ht0, ht1⟩ := ht V k hk
    refine ⟨Finsupp.single (ULift.up t) (R.map k.op b), ?_⟩
    have hp := presheafBoundary_zero_single.{u, v, r} R U V t (R.map k.op b)
    rw [ht0, ht1] at hp
    have hr : (freeObj.{u, v, r} R (U _⦋0⦌)).map k.op
        (Finsupp.single a b - Finsupp.single (g a) b) =
        Finsupp.single (ULift.up (k ≫ a.down)) (R.map k.op b) -
          Finsupp.single (ULift.up (k ≫ (g a).down)) (R.map k.op b) := by
      rw [map_sub]
      exact congrArg₂ (fun x y ↦ x - y)
        (freeObj_map_single.{u, v, r} R (U _⦋0⦌) k.op a b)
        (freeObj_map_single.{u, v, r} R (U _⦋0⦌) k.op (g a) b)
    exact hp.trans hr.symm
  have hall (x : A →₀ R.obj (op T)) :
      LocallyInRange R J (presheafBoundary R U 0) T (x - Finsupp.mapDomain g x) := by
    induction x using Finsupp.induction with
    | zero => simpa using locallyInRange_zero R J (presheafBoundary R U 0) T
    | @single_add a b x ha hb hx =>
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rw [show Finsupp.single a b + x - (Finsupp.single (g a) b + Finsupp.mapDomain g x) =
        (Finsupp.single a b - Finsupp.single (g a) b) + (x - Finsupp.mapDomain g x) by abel]
      exact locallyInRange_add R J _ T (hlocal a b) hx
  have hgz : Finsupp.mapDomain g z = 0 := by
    change Finsupp.mapDomain (Function.invFun f ∘ f) z = 0
    rw [Finsupp.mapDomain_comp]
    change Finsupp.mapDomain (Function.invFun f) ((freeMap R (e.app (op ⦋0⦌))).app (op T) z) = 0
    rw [hz, Finsupp.mapDomain_zero]
  simpa only [hgz, sub_zero] using hall z


end CategoryTheory.RingedHypercover

namespace CategoryTheory.RingedHypercover
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (R : Cᵒᵖ ⥤ RingCat.{r})

/-- Change coefficients and relabel a finitely supported function, additively. -/
private noncomputable def transportFree {A B : Type*} {D E : Type*}
    [AddCommGroup D] [AddCommGroup E]
    (σ : D →+ E) (f : A → B) : (A →₀ D) →+ (B →₀ E) :=
  (Finsupp.mapDomain.addMonoidHom f).comp (Finsupp.mapRange.addMonoidHom σ)

@[simp]
private lemma transportFree_single {A B : Type*} {D E : Type*} [AddCommGroup D] [AddCommGroup E]
    (σ : D →+ E) (f : A → B) (a : A) (x : D) :
    transportFree σ f (Finsupp.single a x) = Finsupp.single (f a) (σ x) := by
  simp [transportFree]

set_option backward.isDefEq.respectTransparency false in
private lemma positive_cycle_locally_boundary (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W) (hcover : HasLocalLifts J W U e)
    (n : ℕ) (T : C) (z : ULift.{max u v r} (T ⟶ U _⦋n + 1⦌) →₀ R.obj (op T))
    (hz : (presheafBoundary R U n).app (op T) z = 0) :
    LocallyInRange R J (presheafBoundary R U (n + 1)) T z := by
  classical
  by_cases hz0 : z = 0
  · rw [hz0]
    exact locallyInRange_zero R J _ T
  obtain ⟨K, hK, hcone⟩ := finite_local_cones.{u, max u v r} J W U e hcover n T
    z.support (Finsupp.support_nonempty_iff.mpr hz0)
  refine ⟨K, hK, fun V f hf ↦ ?_⟩
  obtain ⟨c, b, hcb⟩ := hcone V f hf
  let σ := (R.map f.op).hom.toAddMonoidHom
  let Lc := transportFree σ (fun a ↦ ULift.up (c a))
  let Lb : (ULift.{max u v r} (T ⟶ U _⦋n⦌) →₀ R.obj (op T)) →+
      (ULift.{max u v r} (V ⟶ U _⦋n + 1⦌) →₀ R.obj (op V)) :=
    transportFree σ (fun a ↦ ULift.up (b a))
  let DV : (ULift.{max u v r} (V ⟶ U _⦋n + 2⦌) →₀ R.obj (op V)) →+
      (ULift.{max u v r} (V ⟶ U _⦋n + 1⦌) →₀ R.obj (op V)) :=
    (presheafBoundary R U (n + 1)).app (op V) |>.hom.toAddMonoidHom
  let DT : (ULift.{max u v r} (T ⟶ U _⦋n + 1⦌) →₀ R.obj (op T)) →+
      (ULift.{max u v r} (T ⟶ U _⦋n⦌) →₀ R.obj (op T)) :=
    (presheafBoundary R U n).app (op T) |>.hom.toAddMonoidHom
  let res : (ULift.{max u v r} (T ⟶ U _⦋n + 1⦌) →₀ R.obj (op T)) →+
      (ULift.{max u v r} (V ⟶ U _⦋n + 1⦌) →₀ R.obj (op V)) :=
    (freeObj R (U _⦋n + 1⦌)).map f.op |>.hom.toAddMonoidHom
  refine ⟨Lc z, ?_⟩
  have hsingle (a : ULift.{max u v r} (T ⟶ U _⦋n + 1⦌)) (ha : a ∈ z.support)
      (x : R.obj (op T)) :
      DV (Lc (Finsupp.single a x)) + Lb (DT (Finsupp.single a x)) =
        res (Finsupp.single a x) := by
    obtain ⟨hc0, hcs⟩ := hcb a ha
    have hLc : Lc (Finsupp.single a x) = Finsupp.single (ULift.up (c a)) (σ x) :=
      transportFree_single _ _ _ _
    have hLb (i : Fin (n + 2)) :
        Lb (Finsupp.single (ULift.up (a.down ≫ U.δ i)) x) =
          Finsupp.single (ULift.up (b (ULift.up (a.down ≫ U.δ i)))) (σ x) :=
      transportFree_single _ _ _ _
    rw [hLc]
    have hD := presheafBoundary_single.{u, v, r} R U (n + 1) V (c a) (σ x)
    change DV _ = _ at hD
    rw [hD]
    have hD' := presheafBoundary_single.{u, v, r} R U n T a.down x
    change DT _ = _ at hD'
    rw [hD', map_sum]
    simp only [map_zsmul, hLb]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_zsmul, hc0, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, hcs, Finset.sum_neg_distrib]
    rw [add_assoc, neg_add_cancel, add_zero]
    exact (freeObj_map_single.{u, v, r} R (U _⦋n + 1⦌) f.op a x).symm
  have hsum := Finset.sum_congr (s₁ := z.support) (s₂ := z.support) rfl
    (fun a ha ↦ hsingle a ha (z a))
  have hzsum : ∑ a ∈ z.support, Finsupp.single a (z a) = z := Finsupp.sum_single z
  simp only [Finset.sum_add_distrib, ← map_sum, hzsum] at hsum
  change DT z = 0 at hz
  rw [hz, map_zero, add_zero] at hsum
  exact hsum


end CategoryTheory.RingedHypercover

namespace CategoryTheory

private theorem exact_of_dual_shortComplex
    {A : Type*} [Category A] [Abelian A] (S : ShortComplex A) (hS : S.Exact)
    (I : A) [Injective I]
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (e₁ : (S.X₃ ⟶ I) ≃+ X) (e₂ : (S.X₂ ⟶ I) ≃+ Y) (e₃ : (S.X₁ ⟶ I) ≃+ Z)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a, e₂ (S.g ≫ a) = f (e₁ a))
    (hg : ∀ a, e₃ (S.f ≫ a) = g (e₂ a)) : Function.Exact f g := by
  intro y
  constructor
  · intro hy
    let a := e₂.symm y
    have ha : S.f ≫ a = 0 := by
      apply e₃.injective
      rw [map_zero, hg]
      simpa only [a, e₂.apply_symm_apply] using hy
    refine ⟨e₁ (hS.descToInjective a ha), ?_⟩
    rw [← hf, hS.comp_descToInjective]
    exact e₂.apply_symm_apply y
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := e₁.surjective x
    rw [← hf, ← hg, ← Category.assoc, S.zero, Limits.zero_comp, map_zero]

/-- The canonical augmented alternating section sequence of an injective module sheaf
on a representable hypercover is exact, without affineness or weak contractibility.

Source: Stacks Project, Hypercoverings, Tags 01GE and 01GW, ringed-module analogue
(auxiliary; not a blueprint node).

The matching condition says that each tuple of lower simplices over `w : T ⟶ W`
lifts on a covering sieve. For `n = 0` there are no lower simplices. For `n = 1`
it says that two vertices with the same augmentation lift locally to an edge.
In higher degrees it is local surjectivity onto the finite matching limit;
including all lower simplex operators includes the degenerate faces determined
by the proper faces. On a subcanonical site this is exactly the sheaf-epimorphism
condition, by the sectionwise-limit and locally-surjective-epi lemmas in the proof DAG.

Proof:
1. Construct represented free module presheaves explicitly as ULift-indexed finitely
   supported functions, and prove their additive Yoneda equivalence. Sheafification
   gives the represented free module sheaves; alternating face maps square to zero.
2. The augmentation is locally surjective by degree-zero matching lifts. Its kernel
   is locally generated by differences of vertices with the same augmentation, and
   degree-one matching lifts write these differences as boundaries.
3. A positive-degree cycle has finite support. The theorem `finite_local_cones` provides
   two adjacent cone functions on the original finite labels after a covering refinement.
   Its proof converts compatible face tuples to complete lower-simplex matching families
   and inductively lifts those families. The alternating cone identity shows that the
   restricted cycle is a boundary, even when labels coincide after restriction.
4. A locally surjective presheaf-module map becomes epi after sheafification: use the
   adjunction and the separatedness of sheaves to cancel two maps from its codomain.
   Apply this to the lift to the kernel. Preservation of kernels and the epi-kernel-lift
   criterion give exactness of the sheafified augmented free resolution.
5. Sheafification adjunction and additive Yoneda identify Hom(F_A,I) with I(A).
   Precomposition becomes the displayed alternating sum or restriction augmentation.
   Exactness and injectivity extend each dual cocycle across the preceding image.
   The free-sheaf augmentation is epi, so its dual augmentation is injective.

All these steps are proved in this module and its finite-cone proof import. -/
theorem ringedHypercover_injective_augmentation_exact_ring
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (R : Sheaf J.toGrothendieck RingCat.{r})
    (I : SheafOfModules.{max u v r} R) [Injective I]
    (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ J.toGrothendieck T ∧
        ∀ (V : C) (f : V ⟶ T), S f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ) :
    Function.Injective (I.val.map (e.app (op (SimplexCategory.mk 0))).op) ∧
    Function.Exact
      (I.val.map (e.app (op (SimplexCategory.mk 0))).op)
      (fun s : I.val.obj (op (U _⦋0⦌)) ↦
        ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) ∧
    ∀ n : ℕ, Function.Exact
      (fun s : I.val.obj (op (U _⦋n⦌)) ↦
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
      (fun s : I.val.obj (op (U _⦋n + 1⦌)) ↦
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) := by
  classical
  let K := J.toGrothendieck
  let S : Sheaf K RingCat.{r} := R
  let : HasSheafify K AddCommGrpCat.{max u v r} := by
    let q : C ≌ AsSmall.{max u v r} C := AsSmall.equiv
    let L := q.inverse.inducedTopology K
    have : HasSheafify L AddCommGrpCat.{max u v r} := by infer_instance
    exact q.hasSheafify K L _
  let : K.WEqualsLocallyBijective AddCommGrpCat.{max u v r} := by
    let q : C ≌ AsSmall.{max u v r} C := AsSmall.equiv
    let L := q.inverse.inducedTopology K
    have : L.WEqualsLocallyBijective AddCommGrpCat.{max u v r} := by infer_instance
    exact GrothendieckTopology.WEqualsLocallyBijective.transport K L q.inverse
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  let F := RingedHypercover.freeSheafFunctor.{u, v, r} K S
  let E (A : C) := RingedHypercover.sectionEquiv K S A I
  have hloc : ∃ Q : Sieve W, Q ∈ K W ∧ ∀ (V : C) (f : V ⟶ W), Q f →
      ∃ t : V ⟶ U _⦋0⦌, t ≫ e.app (op ⦋0⦌) = f := by
    obtain ⟨Q, hQ, ht⟩ := hcover 0 W (𝟙 W)
      (fun Δ h ↦ False.elim (Nat.not_lt_zero _ h))
      (by intro Δ h; omega) (by intro Δ Δ' h; omega)
    refine ⟨Q, hQ, fun V f hf ↦ ?_⟩
    obtain ⟨t, ht, _⟩ := ht V f hf
    exact ⟨t, by simpa using ht⟩
  have hepi : Epi (F.map (e.app (op ⦋0⦌))) :=
    RingedHypercover.augmentation_epi_of_local_lifts K S W U e hloc
  have hzero := RingedHypercover.augmentation_exact_of_local_boundaries K S W U e
    (RingedHypercover.augmentation_kernel_locally_boundary K S.obj W U e hcover)
  have hpos (n : ℕ) := RingedHypercover.positive_exact_of_local_boundaries K S U n
    (RingedHypercover.positive_cycle_locally_boundary K S.obj W U e hcover n)
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (E W).symm.injective
    apply (cancel_epi (F.map (e.app (op ⦋0⦌)))).mp
    apply (E (U _⦋0⦌)).injective
    rw [RingedHypercover.sectionEquiv_precomp, RingedHypercover.sectionEquiv_precomp]
    change I.val.map (e.app (op ⦋0⦌)).op ((E W) ((E W).symm x)) =
      I.val.map (e.app (op ⦋0⦌)).op ((E W) ((E W).symm y))
    simpa only [AddEquiv.apply_symm_apply] using hxy
  · apply exact_of_dual_shortComplex
      (RingedHypercover.augmentationShortComplex K S W U e) hzero I
      (E W) (E (U _⦋0⦌)) (E (U _⦋1⦌))
    · exact RingedHypercover.sectionEquiv_precomp K S (e.app (op ⦋0⦌)) I
    · exact RingedHypercover.sectionEquiv_boundary K S U 0 I
  · intro n
    apply exact_of_dual_shortComplex (RingedHypercover.shortComplex K S U n) (hpos n) I
      (E (U _⦋n⦌)) (E (U _⦋n + 1⦌)) (E (U _⦋n + 2⦌))
    · exact RingedHypercover.sectionEquiv_boundary K S U n I
    · exact RingedHypercover.sectionEquiv_boundary K S U (n + 1) I

end CategoryTheory
