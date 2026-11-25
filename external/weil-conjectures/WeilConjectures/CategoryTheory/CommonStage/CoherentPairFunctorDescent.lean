/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.CategoryTheory.StageSystem.Preadditive
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Lattice

/-! # Coherent common-stage pair functor descent

Source: blueprint sketches 32, finite common-stage principle, and 42,
Proposition `prop:pseudocone-functor`, Theorems `thm:pair-universal` and
`thm:karoubi-universal` (blueprint: lem-sbc-coherent-pair-functor-descent).
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CommonStage

-- Bundling the category carriers puts both independent category universes in a maximum.
set_option linter.checkUnivs false in
/-- Normalized additive transition diagrams. Source: sketch 42, finite-stage transitions
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Diagram (I : Type w) [PartialOrder I] where
  C : I → Type u
  [category : ∀ i, Category.{v} (C i)]
  [preadditive : ∀ i, Preadditive (C i)]
  [biproducts : ∀ i, HasFiniteBiproducts (C i)]
  U : ∀ {i j}, i ≤ j → C i ⥤ C j
  [additive : ∀ {i j} (h : i ≤ j), (U h).Additive]
  unit : ∀ i, U (le_refl i) = 𝟭 (C i)
  a : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k), U h ⋙ U h' ≅ U (h.trans h')
  a_left : ∀ {i j} (h : i ≤ j),
    a (le_refl i) h =
      Functor.isoWhiskerRight (eqToIso (unit i)) (U h) ≪≫ (U h).leftUnitor
  a_right : ∀ {i j} (h : i ≤ j),
    a h (le_refl j) =
      Functor.isoWhiskerLeft (U h) (eqToIso (unit j)) ≪≫ (U h).rightUnitor
  pentagon : ∀ {i j k l} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
    (U h'').map ((a h h').hom.app X) ≫ (a (h.trans h') h'').hom.app X =
      (a h' h'').hom.app ((U h).obj X) ≫ (a h (h'.trans h'')).hom.app X

attribute [instance] Diagram.category Diagram.preadditive Diagram.biproducts Diagram.additive

variable {I : Type w} [PartialOrder I]

/-- Pair objects. Source: sketch 42, Definition `def:pair-objects`
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Pair (A : Diagram.{w, u, v} I) := Σ i, A.C i

/-- A common-stage representative. Source: sketch 42, common-stage morphism representatives
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Rep (A : Diagram.{w, u, v} I) (X Y : Pair A) where
  stage : I
  source_le : X.1 ≤ stage
  target_le : Y.1 ≤ stage
  arrow : (A.U source_le).obj X.2 ⟶ (A.U target_le).obj Y.2

/-- Transport by the specified associators, with the inverse on the source.
Source: sketch 42, transport (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def transport {A : Diagram.{w, u, v} I} {X Y : Pair A} (r : Rep A X Y)
    {n : I} (h : r.stage ≤ n) :
    (A.U (r.source_le.trans h)).obj X.2 ⟶ (A.U (r.target_le.trans h)).obj Y.2 :=
  (A.a r.source_le h).inv.app X.2 ≫ (A.U h).map r.arrow ≫
    (A.a r.target_le h).hom.app Y.2

/-- Equality after transport to a common overfield. Source: sketch 42, common-stage equality
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def EventuallyEqual {A : Diagram.{w, u, v} I} {X Y : Pair A}
    (r s : Rep A X Y) : Prop :=
  ∃ (n : I) (h : r.stage ≤ n) (h' : s.stage ≤ n), transport r h = transport s h'

/-- The actual quotient of representatives; no choice of a category is hidden in its Hom sets.
Source: sketch 42, pair morphisms (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Hom (A : Diagram.{w, u, v} I) (X Y : Pair A) := Quot (@EventuallyEqual I _ A X Y)

/-- The class of a representative. Source: sketch 42, pair morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def repr {A : Diagram.{w, u, v} I} {X Y : Pair A} (r : Rep A X Y) : Hom A X Y :=
  Quot.mk _ r

/-- Operations and laws on the explicit quotient Hom types.
Source: sketch 42 (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure PairStructure (A : Diagram.{w, u, v} I) where
  [group : ∀ X Y : Pair A, AddCommGroup (Hom A X Y)]
  id : ∀ X : Pair A, Hom A X X
  comp : ∀ {X Y Z : Pair A}, Hom A X Y → Hom A Y Z → Hom A X Z
  id_comp : ∀ {X Y : Pair A} (f : Hom A X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Pair A} (f : Hom A X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : Pair A} (f : Hom A W X) (g : Hom A X Y) (h : Hom A Y Z),
    comp (comp f g) h = comp f (comp g h)
  add_comp : ∀ {X Y Z : Pair A} (f g : Hom A X Y) (h : Hom A Y Z),
    comp (f + g) h = comp f h + comp g h
  comp_add : ∀ {X Y Z : Pair A} (f : Hom A X Y) (g h : Hom A Y Z),
    comp f (g + h) = comp f g + comp f h

/-- The category carrier records which canonical operations are in use.
Source: sketch 42, pair category (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def PairStructure.Obj {A : Diagram.{w, u, v} I} (_R : PairStructure A) := Pair A

/-- Category structure assembled from the stated pair laws, with the actual quotient Hom.
Source: sketch 42, composition laws (blueprint: lem-sbc-coherent-pair-functor-descent). -/
instance pairCategory {A : Diagram.{w, u, v} I} (R : PairStructure A) : Category R.Obj where
  Hom := Hom A
  id := R.id
  comp := R.comp
  id_comp := R.id_comp
  comp_id := R.comp_id
  assoc := R.assoc

/-- Preadditivity assembled from the pair laws. Source: sketch 42, composition laws
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
instance pairPreadditive {A : Diagram.{w, u, v} I} (R : PairStructure A) :
    Preadditive R.Obj where
  homGroup := R.group
  add_comp := fun _ _ _ ↦ R.add_comp
  comp_add := fun _ _ _ ↦ R.comp_add

/-- The class map with its categorical type made explicit. Source: sketch 42, pair morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def PairStructure.repr {A : Diagram.{w, u, v} I} (R : PairStructure A)
    {X Y : R.Obj} (r : Rep A X Y) : X ⟶ Y := CategoryTheory.CommonStage.repr r

/-- Stage functors with specified comparison isomorphisms, before imposing coherence.
Source: sketch 42, pseudocone comparisons (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Family (A B : Diagram.{w, u, v} I) where
  φ : ∀ i, A.C i ⥤ B.C i
  [additive : ∀ i, (φ i).Additive]
  b : ∀ {i j} (h : i ≤ j), φ i ⋙ B.U h ≅ A.U h ⋙ φ j

attribute [instance] Family.additive

/-- The normalized unit and tower equations, retaining both diagrams' associators.
Source: sketch 42, pseudocone tower (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Family.Coherent {A B : Diagram.{w, u, v} I} (Φ : Family A B) : Prop where
  unit : ∀ i,
    Φ.b (le_refl i) =
      Functor.isoWhiskerLeft (Φ.φ i) (eqToIso (B.unit i)) ≪≫ (Φ.φ i).rightUnitor ≪≫
        (Φ.φ i).leftUnitor.symm ≪≫
          Functor.isoWhiskerRight (eqToIso (A.unit i)).symm (Φ.φ i)
  tower : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) (X : A.C i),
    (B.a h h').hom.app ((Φ.φ i).obj X) ≫ (Φ.b (h.trans h')).hom.app X =
      (B.U h').map ((Φ.b h).hom.app X) ≫
        (Φ.b h').hom.app ((A.U h).obj X) ≫ (Φ.φ k).map ((A.a h h').hom.app X)

/-- The descended object formula. Source: sketch 42, pseudocone functor
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.obj {A B : Diagram.{w, u, v} I} (Φ : Family A B) (X : Pair A) : Pair B :=
  ⟨X.1, (Φ.φ X.1).obj X.2⟩

/-- The descended representative formula, with `b` at the source and its inverse at the target.
Source: sketch 42, pseudocone functor (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.rep {A B : Diagram.{w, u, v} I} (Φ : Family A B) {X Y : Pair A}
    (r : Rep A X Y) : Rep B (Φ.obj X) (Φ.obj Y) where
  stage := r.stage
  source_le := r.source_le
  target_le := r.target_le
  arrow := (Φ.b r.source_le).hom.app X.2 ≫ (Φ.φ r.stage).map r.arrow ≫
    (Φ.b r.target_le).inv.app Y.2

/-- The identity family, using only canonical unitors.
Source: sketch 42, pair universal property (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.identity (A : Diagram.{w, u, v} I) : Family A A where
  φ i := 𝟭 (A.C i)
  b h := (A.U h).leftUnitor ≪≫ (A.U h).rightUnitor.symm

/-- Composite comparisons are obtained by whiskering the two given comparisons.
Source: sketch 42, pair universal property (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.comp {A B C : Diagram.{w, u, v} I} (Φ : Family A B) (Θ : Family B C) :
    Family A C where
  φ i := Φ.φ i ⋙ Θ.φ i
  b h := (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft (Φ.φ _) (Θ.b h) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Φ.b h) (Θ.φ _) ≪≫
      Functor.associator _ _ _

/-- Compatible transformations are the stage naturality squares with the comparisons.
Source: sketch 42, pseudocone morphisms (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Compatible {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) : Prop :=
  ∀ {i j} (h : i ≤ j) (X : A.C i),
    (Φ.b h).hom.app X ≫ (η j).app ((A.U h).obj X) =
      (B.U h).map ((η i).app X) ≫ (Ψ.b h).hom.app X

/-- Characterization of the functor by its formulas on all objects and representatives.
`HEq` only accommodates the displayed object equality; it imposes equality of the arrows.
Source: sketch 42, pseudocone functor (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure IsDescent {A B : Diagram.{w, u, v} I} (RA : PairStructure A) (RB : PairStructure B)
    (Φ : Family A B) (F : RA.Obj ⥤ RB.Obj) : Prop where
  obj : ∀ X, F.obj X = Φ.obj X
  map : ∀ {X Y : RA.Obj} (r : Rep A X Y),
    HEq (F.map (RA.repr r)) (RB.repr (Φ.rep r))
  additive : F.Additive

/-- The component `[E, η_E,K]`, written using the literal identity transition to make its
source and target types explicit. Source: sketch 42, pseudocone morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def transformationRep {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (X : Pair A) : Rep B (Φ.obj X) (Ψ.obj X) :=
  ⟨X.1, le_refl _, le_refl _, (B.U (le_refl X.1)).map ((η X.1).app X.2)⟩

-- The independently variable object and Hom universes are bundled in the same maximum.
set_option linter.checkUnivs false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private abbrev stageSystem (A : Diagram.{w, u, v} I) : StageSystem A.C where
  T := A.U
  assoc := A.a
  cocycle := A.pentagon

private instance stage_additive (A : Diagram.{w, u, v} I) (i j : I) (h : i ≤ j) :
    ((stageSystem A).T h).Additive := A.additive h

private abbrev stageObj {A : Diagram.{w, u, v} I} (X : Pair A) :
    (stageSystem A).PairCategory := ⟨X.1, X.2⟩

private def repEquiv {A : Diagram.{w, u, v} I} (X Y : Pair A) :
    Rep A X Y ≃ StageSystem.PairCategory.Rep (stageObj X) (stageObj Y) where
  toFun r := ⟨r.stage, r.source_le, r.target_le, r.arrow⟩
  invFun r := ⟨r.k, r.hX, r.hY, r.u⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev homEquiv {A : Diagram.{w, u, v} I} [IsDirectedOrder I] (X Y : Pair A) :
    Hom A X Y ≃ (stageObj X ⟶ stageObj Y) :=
  Quot.congr (repEquiv X Y) (fun _ _ ↦ Iff.rfl)

private noncomputable abbrev pairStructure (A : Diagram.{w, u, v} I) [IsDirectedOrder I] :
    PairStructure A where
  group X Y := (homEquiv X Y).addCommGroup
  id X := (homEquiv X X).symm (𝟙 (stageObj X))
  comp {X Y Z} f g :=
    (homEquiv X Z).symm (homEquiv X Y f ≫ homEquiv Y Z g)
  id_comp {X Y} f := by simp
  comp_id {X Y} f := by simp
  assoc {W X Y Z} f g h := by simp [Category.assoc]
  add_comp {X Y Z} f g h := by
    change (homEquiv X Z).symm
      (homEquiv X Y ((homEquiv X Y).symm (homEquiv X Y f + homEquiv X Y g)) ≫
        homEquiv Y Z h) =
      (homEquiv X Z).symm (homEquiv X Z ((homEquiv X Z).symm
        (homEquiv X Y f ≫ homEquiv Y Z h)) +
        homEquiv X Z ((homEquiv X Z).symm (homEquiv X Y g ≫ homEquiv Y Z h)))
    simp only [Equiv.apply_symm_apply, Preadditive.add_comp]
  comp_add {X Y Z} f g h := by
    change (homEquiv X Z).symm
      (homEquiv X Y f ≫
        homEquiv Y Z ((homEquiv Y Z).symm (homEquiv Y Z g + homEquiv Y Z h))) =
      (homEquiv X Z).symm (homEquiv X Z ((homEquiv X Z).symm
        (homEquiv X Y f ≫ homEquiv Y Z g)) +
        homEquiv X Z ((homEquiv X Z).symm (homEquiv X Y f ≫ homEquiv Y Z h)))
    simp only [Equiv.apply_symm_apply, Preadditive.comp_add]

set_option allowUnsafeReducibility true in
attribute [local reducible] PairStructure.Obj Pair

private noncomputable instance canonicalCategory (A : Diagram.{w, u, v} I)
    [IsDirectedOrder I] : Category.{max w v} (Pair A) := pairCategory (pairStructure A)

private noncomputable instance canonicalPreadditive (A : Diagram.{w, u, v} I)
    [IsDirectedOrder I] : Preadditive (Pair A) := pairPreadditive (pairStructure A)

private abbrev compareFunctor (A : Diagram.{w, u, v} I) [IsDirectedOrder I] :
    (pairStructure A).Obj ⥤ (stageSystem A).PairCategory where
  obj := stageObj
  map := homEquiv _ _
  map_id _ := (homEquiv _ _).apply_symm_apply _
  map_comp _ _ := (homEquiv _ _).apply_symm_apply _

private theorem compare_injective {A : Diagram.{w, u, v} I} [IsDirectedOrder I]
    {X Y : (pairStructure A).Obj} : Function.Injective ((compareFunctor A).map (X := X) (Y := Y)) :=
  (homEquiv X Y).injective

private noncomputable abbrev inverseFunctor (A : Diagram.{w, u, v} I) [IsDirectedOrder I] :
    (stageSystem A).PairCategory ⥤ (pairStructure A).Obj where
  obj X := ⟨X.stage, X.obj⟩
  map {X Y} f := (homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change (homEquiv ⟨X.stage, X.obj⟩ ⟨Z.stage, Z.obj⟩).symm (f ≫ g) =
      (homEquiv ⟨X.stage, X.obj⟩ ⟨Z.stage, Z.obj⟩).symm
        (homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩
          ((homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm f) ≫
        homEquiv ⟨Y.stage, Y.obj⟩ ⟨Z.stage, Z.obj⟩
          ((homEquiv ⟨Y.stage, Y.obj⟩ ⟨Z.stage, Z.obj⟩).symm g))
    simp only [Equiv.apply_symm_apply]

private instance inverse_additive (A : Diagram.{w, u, v} I) [IsDirectedOrder I] :
    (inverseFunctor A).Additive where
  map_add {X Y} f g := by
    change (homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm (f + g) =
      (homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm
        (homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩
          ((homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm f) +
        homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩
          ((homEquiv ⟨X.stage, X.obj⟩ ⟨Y.stage, Y.obj⟩).symm g))
    simp only [Equiv.apply_symm_apply]

private abbrev stageMorphism {A B : Diagram.{w, u, v} I} (Φ : Family A B)
    (hΦ : Φ.Coherent) : (stageSystem A).Morphism (stageSystem B) where
  Φ := Φ.φ
  β := Φ.b
  coh h h' X := (hΦ.tower h h' X).symm

private noncomputable abbrev descend {A B : Diagram.{w, u, v} I} [IsDirectedOrder I]
    (Φ : Family A B) (hΦ : Φ.Coherent) :
    (pairStructure A).Obj ⥤ (pairStructure B).Obj where
  obj := Φ.obj
  map {X Y} f := (homEquiv (Φ.obj X) (Φ.obj Y)).symm
    ((stageMorphism Φ hΦ).functor.map (homEquiv X Y f))
  map_id X := by
    change (homEquiv (Φ.obj X) (Φ.obj X)).symm ((stageMorphism Φ hΦ).functor.map
      (homEquiv X X ((homEquiv X X).symm (𝟙 _)))) =
      (homEquiv (Φ.obj X) (Φ.obj X)).symm (𝟙 _)
    simp only [Equiv.apply_symm_apply, Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    change (homEquiv (Φ.obj X) (Φ.obj Z)).symm ((stageMorphism Φ hΦ).functor.map
      (homEquiv X Z ((homEquiv X Z).symm (homEquiv X Y f ≫ homEquiv Y Z g)))) =
      (homEquiv (Φ.obj X) (Φ.obj Z)).symm
        (homEquiv (Φ.obj X) (Φ.obj Y) ((homEquiv (Φ.obj X) (Φ.obj Y)).symm _) ≫
        homEquiv (Φ.obj Y) (Φ.obj Z) ((homEquiv (Φ.obj Y) (Φ.obj Z)).symm _))
    simp only [Equiv.apply_symm_apply, Functor.map_comp]

private def stageTransformation {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
    (hη : Compatible η) : (stageMorphism Φ hΦ).Hom (stageMorphism Ψ hΨ) where
  τ := η
  comm h X := (hη h X).symm

private noncomputable def transformation {A B : Diagram.{w, u, v} I} [IsDirectedOrder I]
    {Φ Ψ : Family A B} (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent)
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (hη : Compatible η) :
    descend Φ hΦ ⟶ descend Ψ hΨ where
  app X := (pairStructure B).repr (transformationRep η X)
  naturality {X Y} f := by
    apply compare_injective
    change homEquiv _ _ ((homEquiv _ _).symm
      (homEquiv _ _ ((descend Φ hΦ).map f) ≫
        homEquiv _ _ ((pairStructure B).repr (transformationRep η Y)))) =
      homEquiv _ _ ((homEquiv _ _).symm
        (homEquiv _ _ ((pairStructure B).repr (transformationRep η X)) ≫
          homEquiv _ _ ((descend Ψ hΨ).map f)))
    simp only [Equiv.apply_symm_apply]
    exact (StageSystem.Morphism.descNatTrans
      (stageTransformation hΦ hΨ η hη)).naturality (homEquiv X Y f)

end CategoryTheory.CommonStage
