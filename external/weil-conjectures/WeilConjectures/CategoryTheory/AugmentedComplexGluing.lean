/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Effective gluing of augmented complexes of module sheaves

Source: Stacks Project, Sites, Tag 04TR, applied degreewise, and algebraization,
Tag 099E, the gluing of the complexes K_U.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}} {A : Type u} {U : A → C}

/-- Restricting module sheaves to each slice preserves zero morphisms.
Source: the sectionwise definition of slice restriction.
(auxiliary; not a blueprint node). -/
instance augmentedComplexGlueData_over_preservesZeroMorphisms
    (R : Sheaf J RingCat.{u}) {A : Type u} (U : A → C) :
    ∀ i, (overFunctor.{u} R (U i)).PreservesZeroMorphisms :=
  fun i ↦ ⟨by intro M N; ext V x; rfl⟩

/-- Strict descent data for augmented complexes on slices of a ringed site.
All transitions are specified on sections over test spans, avoiding any choice of
fibre products. Their equations express chain compatibility and the augmentation square.
Source: Stacks Project, Tag 04TR and algebraization, Tag 099E.
(auxiliary; not a blueprint node). -/
structure AugmentedComplexGlueData (R : Sheaf J RingCat.{u}) {A : Type u} (U : A → C)
    [∀ i, (overFunctor R (U i)).PreservesZeroMorphisms]
    (B : CochainComplex (SheafOfModules.{u} R) ℤ)
    (localComplex : ∀ i : A, CochainComplex (SheafOfModules.{u} (R.over (U i))) ℤ)
    (localAugmentation : ∀ i : A,
      localComplex i ⟶ ((overFunctor R (U i)).mapHomologicalComplex (.up ℤ)).obj B) where
  transition : ∀ (n : ℤ) (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
    ((localComplex i).X n).val.obj (op (Over.mk a)) ≃ₗ[R.obj.obj (op W)]
      ((localComplex j).X n).val.obj (op (Over.mk b))
  naturality : ∀ (n : ℤ) (i j : A) (W V : C) (k : V ⟶ W)
    (a : W ⟶ U i) (b : W ⟶ U j)
    (x : ((localComplex i).X n).val.obj (op (Over.mk a))),
    transition n i j V (k ≫ a) (k ≫ b)
      (((localComplex i).X n).val.map
        (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
      ((localComplex j).X n).val.map
        (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
          (transition n i j W a b x)
  cocycle : ∀ (n : ℤ) (i j k : A) (W : C)
    (a : W ⟶ U i) (b : W ⟶ U j) (c : W ⟶ U k)
    (x : ((localComplex i).X n).val.obj (op (Over.mk a))),
    transition n i k W a c x = transition n j k W b c (transition n i j W a b x)
  differential : ∀ (n k : ℤ) (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j)
    (x : ((localComplex i).X n).val.obj (op (Over.mk a))),
    transition k i j W a b (((localComplex i).d n k).val.app (op (Over.mk a)) x) =
      ((localComplex j).d n k).val.app (op (Over.mk b)) (transition n i j W a b x)
  augmentation : ∀ (n : ℤ) (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j)
    (x : ((localComplex i).X n).val.obj (op (Over.mk a))),
    ((localAugmentation j).f n).val.app (op (Over.mk b)) (transition n i j W a b x) =
      ((localAugmentation i).f n).val.app (op (Over.mk a)) x

private abbrev gluedModule (G : ModuleGlueData.{u, u, u, u, u} R U) : SheafOfModules.{u} R :=
  G.sheaf G.presheaf_isSheaf

private def tupleMap (G H : ModuleGlueData.{u, u, u, u, u} R U)
    (α : ∀ i, G.localSheaf i ⟶ H.localSheaf i)
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      H.transition i j W a b ((α i).val.app (op (Over.mk a)) x) =
        (α j).val.app (op (Over.mk b)) (G.transition i j W a b x))
    (V : C) : G.tuples V →ₗ[R.obj.obj (op V)] H.tuples V where
  toFun x := ⟨fun q ↦ (α q.1).val.app (op (Over.mk q.2.2.2)) (x.1 q), by
    constructor
    · intro i W T k f a
      change (H.localSheaf i).val.map
          (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op
          ((α i).val.app (op (Over.mk a)) (x.1 ⟨i, W, f, a⟩)) = _
      rw [← PresheafOfModules.naturality_apply]
      exact congrArg ((α i).val.app (op (Over.mk (k ≫ a)))) (x.2.1 i W T k f a)
    · intro i j W f a b
      rw [hα, x.2.2]⟩
  map_add' x y := by
    apply Subtype.ext
    funext q
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    funext q
    exact (α q.1).val.app (op (Over.mk q.2.2.2)) |>.hom.map_smul _ _

private def glueMap (G H : ModuleGlueData.{u, u, u, u, u} R U)
    (α : ∀ i, G.localSheaf i ⟶ H.localSheaf i)
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      H.transition i j W a b ((α i).val.app (op (Over.mk a)) x) =
        (α j).val.app (op (Over.mk b)) (G.transition i j W a b x)) :
    gluedModule G ⟶ gluedModule H where
  val :=
    { app := fun V ↦ ModuleCat.ofHom (tupleMap G H α hα V.unop)
      naturality := by
        intro V W f
        ext x
        apply Subtype.ext
        funext q
        rfl }

private theorem glueMap_over (G H : ModuleGlueData.{u, u, u, u, u} R U)
    (α : ∀ i, G.localSheaf i ⟶ H.localSheaf i)
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      H.transition i j W a b ((α i).val.app (op (Over.mk a)) x) =
        (α j).val.app (op (Over.mk b)) (G.transition i j W a b x)) (i : A) :
    (overFunctor R (U i)).map (glueMap G H α hα) ≫
      (H.overIso H.presheaf_isSheaf i).hom =
        (G.overIso G.presheaf_isSheaf i).hom ≫ α i := by
  ext V x
  rfl

private def globalData (M : SheafOfModules.{u} R) : ModuleGlueData.{u, u, u, u, u} R U where
  localSheaf i := M.over (U i)
  transition _ _ _ _ _ := AddEquiv.refl _
  transition_smul := by intros; rfl
  naturality := by intros; rfl
  cocycle := by intros; rfl

private def globalDiagonal (M : SheafOfModules.{u} R) : M ⟶ gluedModule (globalData (U := U) M)
    where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ⟨fun q ↦ M.val.map q.2.2.1.op x, by
            constructor
            · intro i W T k f a
              change M.val.map k.op (M.val.map f.op x) = M.val.map (k ≫ f).op x
              exact (M.val.map_comp_apply f.op k.op x).symm
            · intros
              rfl⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            funext q
            exact map_add _ _ _
          map_smul' := by
            intro r x
            apply Subtype.ext
            funext q
            exact M.val.map_smul _ _ _ }
      naturality := by
        intro V W f
        ext x
        apply Subtype.ext
        funext q
        change M.val.map q.2.2.1.op (M.val.map f x) =
          M.val.map (f ≫ q.2.2.1.op) x
        exact (M.val.map_comp_apply f q.2.2.1.op x).symm }

private theorem globalDiagonal_over (M : SheafOfModules.{u} R) (i : A) :
    (overFunctor R (U i)).map (globalDiagonal (U := U) M) ≫
      ((globalData (U := U) M).overIso (globalData M).presheaf_isSheaf i).hom =
        𝟙 (M.over (U i)) := by
  ext V x
  change M.val.map (𝟙 V.unop.left).op x = x
  simp

private theorem globalDiagonal_isIso (hU : J.CoversTop U) (M : SheafOfModules.{u} R) :
    IsIso (globalDiagonal (U := U) M) := by
  have hlocal (i : A) : IsIso ((overFunctor R (U i)).map (globalDiagonal (U := U) M)) := by
    have he := globalDiagonal_over (U := U) M i
    have heq : (overFunctor R (U i)).map (globalDiagonal (U := U) M) =
        ((globalData (U := U) M).overIso (globalData M).presheaf_isSheaf i).inv := by
      rw [← cancel_mono ((globalData (U := U) M).overIso
        (globalData M).presheaf_isSheaf i).hom, he, Iso.inv_hom_id]
    rw [heq]
    infer_instance
  have : IsIso ((toSheaf R).map (globalDiagonal (U := U) M)) := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop hU
    intro i
    change IsIso ((toSheaf (R.over (U i))).map
      ((overFunctor R (U i)).map (globalDiagonal (U := U) M)))
    infer_instance
  exact isIso_of_reflects_iso _ (toSheaf R)

private theorem hom_ext_cover (hU : J.CoversTop U) {M N : SheafOfModules.{u} R}
    {f g : M ⟶ N} (h : ∀ i, (overFunctor R (U i)).map f = (overFunctor R (U i)).map g) :
    f = g := by
  have := globalDiagonal_isIso hU N
  apply (cancel_mono (globalDiagonal (U := U) N)).1
  ext V x
  apply Subtype.ext
  funext q
  change N.val.map q.2.2.1.op (f.val.app V x) =
    N.val.map q.2.2.1.op (g.val.app V x)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact congrArg (fun z ↦ z.val.app (op (Over.mk q.2.2.2))
    (M.val.map q.2.2.1.op x)) (h q.1)

private def glueToGlobal (hU : J.CoversTop U) (G : ModuleGlueData.{u, u, u, u, u} R U)
    (M : SheafOfModules.{u} R) (α : ∀ i, G.localSheaf i ⟶ M.over (U i))
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      (α j).val.app (op (Over.mk b)) (G.transition i j W a b x) =
        (α i).val.app (op (Over.mk a)) x) : gluedModule G ⟶ M :=
  have := globalDiagonal_isIso hU M
  glueMap G (globalData M) α (fun i j W a b x ↦ (hα i j W a b x).symm) ≫
    inv (globalDiagonal (U := U) M)

private theorem glueToGlobal_diagonal (hU : J.CoversTop U)
    (G : ModuleGlueData.{u, u, u, u, u} R U)
    (M : SheafOfModules.{u} R) (α : ∀ i, G.localSheaf i ⟶ M.over (U i))
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      (α j).val.app (op (Over.mk b)) (G.transition i j W a b x) =
        (α i).val.app (op (Over.mk a)) x) :
    glueToGlobal hU G M α hα ≫ globalDiagonal (U := U) M =
      glueMap G (globalData M) α (fun i j W a b x ↦ (hα i j W a b x).symm) := by
  have := globalDiagonal_isIso hU M
  dsimp only [glueToGlobal]
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem glueToGlobal_over (hU : J.CoversTop U)
    (G : ModuleGlueData.{u, u, u, u, u} R U)
    (M : SheafOfModules.{u} R) (α : ∀ i, G.localSheaf i ⟶ M.over (U i))
    (hα : ∀ i j W (a : W ⟶ U i) (b : W ⟶ U j)
      (x : moduleLocalSections G.localSheaf i (Over.mk a)),
      (α j).val.app (op (Over.mk b)) (G.transition i j W a b x) =
        (α i).val.app (op (Over.mk a)) x) (i : A) :
    (overFunctor R (U i)).map (glueToGlobal hU G M α hα) =
      (G.overIso G.presheaf_isSheaf i).hom ≫ α i := by
  calc
    _ = (overFunctor R (U i)).map (glueToGlobal hU G M α hα) ≫
        ((overFunctor R (U i)).map (globalDiagonal (U := U) M) ≫
          ((globalData (U := U) M).overIso (globalData M).presheaf_isSheaf i).hom) := by
      rw [globalDiagonal_over, Category.comp_id]
    _ = (overFunctor R (U i)).map
        (glueToGlobal hU G M α hα ≫ globalDiagonal (U := U) M) ≫
          ((globalData (U := U) M).overIso (globalData M).presheaf_isSheaf i).hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [glueToGlobal_diagonal]
      exact glueMap_over G (globalData M) α _ i

variable [∀ i, (overFunctor R (U i)).PreservesZeroMorphisms]
variable {B : CochainComplex (SheafOfModules.{u} R) ℤ}
variable {L : ∀ i : A, CochainComplex (SheafOfModules.{u} (R.over (U i))) ℤ}
variable {a : ∀ i : A, L i ⟶ ((overFunctor R (U i)).mapHomologicalComplex (.up ℤ)).obj B}

private def termData (D : AugmentedComplexGlueData R U B L a) (n : ℤ) :
    ModuleGlueData.{u, u, u, u, u} R U where
  localSheaf i := (L i).X n
  transition i j W a b := (D.transition n i j W a b).toAddEquiv
  transition_smul := by
    intro i j W a b r x
    exact (D.transition n i j W a b).map_smul r x
  naturality := D.naturality n
  cocycle := D.cocycle n

private def gluedDifferential (D : AugmentedComplexGlueData R U B L a) (n k : ℤ) :
    gluedModule (termData D n) ⟶ gluedModule (termData D k) :=
  glueMap (termData D n) (termData D k) (fun i ↦ (L i).d n k)
    (D.differential n k)

private def gluedComplex (D : AugmentedComplexGlueData R U B L a) :
    CochainComplex (SheafOfModules.{u} R) ℤ where
  X n := gluedModule (termData D n)
  d n k := gluedDifferential D n k
  shape n k h := by
    ext V x
    apply Subtype.ext
    funext q
    change ((L q.1).d n k).val.app (op (Over.mk q.2.2.2)) (x.1 q) = 0
    rw [HomologicalComplex.shape _ n k h]
    rfl
  d_comp_d' n k l _ _ := by
    ext V x
    apply Subtype.ext
    funext q
    have h := congrArg (fun z ↦ z.val.app (op (Over.mk q.2.2.2)))
      ((L q.1).d_comp_d n k l)
    exact ConcreteCategory.congr_hom h (x.1 q)

private theorem gluedDifferential_over (D : AugmentedComplexGlueData R U B L a)
    (n k : ℤ) (i : A) :
    (overFunctor R (U i)).map (gluedDifferential D n k) ≫
      ((termData D k).overIso (termData D k).presheaf_isSheaf i).hom =
        ((termData D n).overIso (termData D n).presheaf_isSheaf i).hom ≫
          (L i).d n k :=
  glueMap_over (termData D n) (termData D k) _ _ i

private def gluedAugmentationF (hU : J.CoversTop U) (D : AugmentedComplexGlueData R U B L a)
    (n : ℤ) : (gluedComplex D).X n ⟶ B.X n :=
  glueToGlobal hU (termData D n) (B.X n) (fun i ↦ (a i).f n)
    (D.augmentation n)

private theorem gluedAugmentationF_over (hU : J.CoversTop U)
    (D : AugmentedComplexGlueData R U B L a) (n : ℤ) (i : A) :
    (overFunctor R (U i)).map (gluedAugmentationF hU D n) =
      ((termData D n).overIso (termData D n).presheaf_isSheaf i).hom ≫
        (a i).f n :=
  glueToGlobal_over hU (termData D n) (B.X n) _ _ i

private def gluedAugmentation (hU : J.CoversTop U) (D : AugmentedComplexGlueData R U B L a) :
    gluedComplex D ⟶ B where
  f := gluedAugmentationF hU D
  comm' n k _ := by
    apply hom_ext_cover hU
    intro i
    calc
      _ = ((termData D n).overIso (termData D n).presheaf_isSheaf i).hom ≫
          (a i).f n ≫ (overFunctor R (U i)).map (B.d n k) := by
        rw [Functor.map_comp, gluedAugmentationF_over, Category.assoc]
      _ = ((termData D n).overIso (termData D n).presheaf_isSheaf i).hom ≫
          (L i).d n k ≫ (a i).f k := by
        simpa only [Functor.mapHomologicalComplex_obj_d, Category.assoc] using congrArg
          (fun z ↦ ((termData D n).overIso (termData D n).presheaf_isSheaf i).hom ≫ z)
          ((a i).comm n k)
      _ = (overFunctor R (U i)).map (gluedDifferential D n k) ≫
          ((termData D k).overIso (termData D k).presheaf_isSheaf i).hom ≫
            (a i).f k := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ (a i).f k) (gluedDifferential_over D n k i).symm
      _ = _ := by
        rw [Functor.map_comp, gluedAugmentationF_over]
        rfl

private def gluedComplexOverIso (D : AugmentedComplexGlueData R U B L a) (i : A) :
    ((overFunctor R (U i)).mapHomologicalComplex (.up ℤ)).obj (gluedComplex D) ≅
      L i :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (termData D n).overIso (termData D n).presheaf_isSheaf i)
    (fun n k _ ↦ (gluedDifferential_over D n k i).symm)

/-- Strict descent data of augmented module complexes are effective on any covering
family of objects. No boundedness or existence of fibre products is required.
Source: Stacks Project, Sites, Tag 04TR; algebraization, Tag 099E.
(auxiliary; not a blueprint node).

Proof: in degree n form the sheaf of compatible tuples supplied by ModuleGlueData.
Apply the local differentials coordinatewise. Their chain equations and their square-zero
relations hold coordinatewise, giving a global complex. The diagonal from a global module
to the tuples of its restrictions is invertible: on each covering slice, evaluation at the
graph is its inverse, and isomorphisms of sheaves are local. Descend each augmentation
component by this diagonal. Its chain equation holds after restriction to each covering
slice, hence globally. Graph evaluation gives the asserted chain isomorphisms and the
augmentation equation. The construction also applies to the empty site and empty covers. -/
theorem exists_augmentedComplex_of_glueData (hU : J.CoversTop U)
    (D : AugmentedComplexGlueData R U B L a) :
    ∃ (K : CochainComplex (SheafOfModules.{u} R) ℤ) (ε : K ⟶ B),
      ∃ e : ∀ i, ((overFunctor R (U i)).mapHomologicalComplex (.up ℤ)).obj K ≅
          L i,
        ∀ i, (e i).hom ≫ a i =
          ((overFunctor R (U i)).mapHomologicalComplex (.up ℤ)).map ε := by
  refine ⟨gluedComplex D, gluedAugmentation hU D, gluedComplexOverIso D, ?_⟩
  intro i
  apply HomologicalComplex.hom_ext
  intro n
  exact (gluedAugmentationF_over hU D n i).symm

end SheafOfModules
