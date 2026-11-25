/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Global Hom tensor comparison normalized to the original derived counit

Source: Stacks Project, Cohomology, Tags 06YJ and 079U.
(blueprint: lem-pc-global-hom-original-counit-normalization).

This API constructs the original universal counit and transports the adjunction
and tensor comparison to it. The legacy global Hom entry points remain unchanged
pending coordinated base-change normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w vC vD uC uD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

/-- A universal derived counit with a fixed target functor.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
structure SchemeHomUniversalCounit
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (L : D ⥤ H) (F : C ⥤ H) (W : MorphismProperty C)
    [Q.IsLocalization W] where
  counit : Q ⋙ L ⟶ F
  isLeftDerived : L.IsLeftDerivedFunctor counit W

/-- Map an isomorphism between additive functors to homotopy categories.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
def schemeHomUnderivedHomotopyIso {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] {E E' : A ⥤ B} [E.Additive] [E'.Additive]
    (e : E ≅ E') : E.mapHomotopyCategory (.up ℤ) ≅ E'.mapHomotopyCategory (.up ℤ) where
  hom := e.hom.mapHomotopyCategory (.up ℤ)
  inv := e.inv.mapHomotopyCategory (.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]

/-- Changing the target functor by its pinned iso preserves the derived property.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomCounit_comp_iso_leftDerived
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (L : D ⥤ H) {F F' : C ⥤ H} (W : MorphismProperty C)
    [Q.IsLocalization W] (ε : Q ⋙ L ⟶ F) (e : F ≅ F')
    (h : L.IsLeftDerivedFunctor ε W) : L.IsLeftDerivedFunctor (ε ≫ e.hom) W := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension] at h ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂ ε (ε ≫ e.hom) e (Iso.refl L)
    (by simp)).mp h


/-- Change of counit in a tensor representative equation.
Source: Stacks, Tag 079U (blueprint: lem-pc-global-hom-original-counit-normalization). -/
private theorem originalCounitTensorEquation
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (L : C ⥤ D) (δ : L ≅ L) {A B U : C} {A' B' U' V : D}
    (τ : L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B) (μ : A ⊗ B ⟶ U)
    (εU ε'U : L.obj U ⟶ U') (εA ε'A : L.obj A ⟶ A')
    (εB ε'B : L.obj B ⟶ B') (ν : A' ⊗ B' ⟶ V) (φ : U' ⟶ V)
    (hU : δ.hom.app U ≫ ε'U = εU) (hA : δ.hom.app A ≫ ε'A = εA)
    (hB : δ.hom.app B ≫ ε'B = εB)
    (hcoord : L.map μ ≫ εU ≫ φ = τ ≫ (εA ⊗ₘ εB) ≫ ν) :
    L.map μ ≫ ε'U ≫ φ =
      (δ.inv.app (A ⊗ B) ≫ τ ≫ (δ.hom.app A ⊗ₘ δ.hom.app B)) ≫
        (ε'A ⊗ₘ ε'B) ≫ ν := by
  apply (cancel_epi (δ.hom.app (A ⊗ B))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [← δ.hom.naturality_assoc, reassoc_of% hU,
    tensorHom_comp_tensorHom_assoc, hA, hB]
  exact hcoord


variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The trailing presentation in the original derived-pullback existence theorem.
Its statement retains every field of that original trailing existential. Proof
irrelevance therefore identifies its chosen witnesses with the original choices.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomOriginalTensorSpec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (E : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj f M)
      (_ : ∀ {M N} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap f a ≫
          eqToHom (h N).symm)
      (_ : E.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback.{u, w} f ⟶
        E.mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) ∧
        (∃ (_ : (derivedPullback f).CommShift ℤ), (derivedPullback f).IsTriangulated) ∧
        ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  have s₀ := (derivedPullback_spec.{u, w} f)
  have s₁ := Classical.choose_spec s₀
  have s₂ := Classical.choose_spec s₁
  have s₃ := Classical.choose_spec s₂
  exact (Classical.choose_spec s₃).2.2.2

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The original underived presentation is the recorded module tensor pullback.
Proof: its original specification records object and map equalities, so functor
extensionality applies. Naming this equality keeps its proof out of counit data.
Source: Stacks, Tag 06YJ
(blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomOriginalUnderived_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Classical.choose (schemeHomOriginalTensorSpec.{u, w} f) =
      Scheme.Modules.tensorPullback f := by
  have s₄ := schemeHomOriginalTensorSpec.{u, w} f
  have s₅ := Classical.choose_spec s₄
  have s₆ := Classical.choose_spec s₅
  exact CategoryTheory.Functor.ext (Classical.choose s₅)
    (fun M N a ↦ @Classical.choose _ _ s₆ M N a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original counit, transported along the recorded equality of module functors.
Only the original presentation is extracted; no second counit is chosen.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
def schemeHomPullbackCounitData {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := SingleComplexBaseChange.tensorPullbackAdditive f
    SchemeHomUniversalCounit
      (C := HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ))
      (D := DerivedCategory.{w, u, u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
      (H := DerivedCategory.{w, u, u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (DerivedCategory.Qh.{w, u, u + 1}
        (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
      (derivedPullback.{u, w} f)
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh.{w, u, u + 1} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :=
  letI := SingleComplexBaseChange.tensorPullbackAdditive f
  let s₄ := schemeHomOriginalTensorSpec.{u, w} f
  let E := Classical.choose s₄
  let s₅ := Classical.choose_spec s₄
  let s₆ := Classical.choose_spec s₅
  let s₇ := Classical.choose_spec s₆
  let hEadd := Classical.choose s₇
  let s₈ := Classical.choose_spec s₇
  let ε := Classical.choose s₈
  let hL := (Classical.choose_spec s₈).1
  let h : E = Scheme.Modules.tensorPullback f := schemeHomOriginalUnderived_eq f
  letI : E.Additive := hEadd
  let ε' : DerivedCategory.Qh.{w, u, u + 1} ⋙ derivedPullback.{u, w} f ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w, u, u + 1} := ε
  let hL' : (derivedPullback.{u, w} f).IsLeftDerivedFunctor ε'
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) := hL
  let e := Functor.isoWhiskerRight (schemeHomUnderivedHomotopyIso (eqToIso h))
    (DerivedCategory.Qh.{w, u, u + 1} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  { counit := ε' ≫ e.hom
    isLeftDerived := schemeHomCounit_comp_iso_leftDerived
      (C := HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ))
      (D := DerivedCategory.{w, u, u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
      (H := DerivedCategory.{w, u, u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
      (DerivedCategory.Qh.{w, u, u + 1} (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
      (derivedPullback.{u, w} f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) ε' e hL' }

attribute [local irreducible] schemeHomPullbackCounitData

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived adjunction normalized to the original derived-pullback counit.
Source: Stacks, Tags 079W and 0B6I (blueprint: lem-pc-global-hom-original-counit-normalization). -/
def schemeHomOriginalPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  let d := schemeHomPullbackCounitData f
  Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := SingleComplexBaseChange.tensorPullbackAdditive f) d.counit d.isLeftDerived)

omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The composition counit has its recorded universal property.
Source: Stacks, Tag 0D5S
(blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomCompositionCounit_isLeftDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).IsLeftDerivedFunctor (SingleComplexBaseChange.counit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) f

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The unique change of presentation from the composition counit to the original one.
Source: Stacks, Tags 06YJ and 079U (blueprint: lem-pc-global-hom-original-counit-normalization). -/
def schemeHomPullbackCounitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ≅ derivedPullback f :=
  let d := schemeHomPullbackCounitData f
  letI := d.isLeftDerived
  letI : (derivedPullback f).IsLeftDerivedFunctor (SingleComplexBaseChange.counit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :=
    schemeHomCompositionCounit_isLeftDerived f
  Functor.leftDerivedUnique (derivedPullback f) (derivedPullback f)
    (SingleComplexBaseChange.counit f) d.counit
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ))

attribute [local irreducible] schemeHomPullbackCounitIso
  schemeHomOriginalPullbackAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived tensor iso transported to the original derived-pullback counit.
The inverse change of presentation acts on the tensor input, and its tensor square
acts on the outputs. Thus arbitrary changes of the composition counit cancel.
Source: Stacks, Tags 079U and 0B6I (blueprint: lem-pc-global-hom-original-counit-normalization). -/
def schemeHomOriginalTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X) :=
  let δ := schemeHomPullbackCounitIso f
  Functor.isoWhiskerLeft (tensor (schemeDerivedCategory Y)) δ.symm ≪≫
    Classical.choose (exists_mixedHomTensorPullbackIso f) ≪≫
    Functor.isoWhiskerRight (NatIso.prod δ δ) (tensor (schemeDerivedCategory X))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The change of presentation intertwines the original and composition counits.
Source: Stacks, Tag 06YJ (blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomPullbackCounitIso_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :
    (schemeHomPullbackCounitIso f).hom.app (DerivedCategory.Qh.obj P) ≫
      (schemeHomPullbackCounitData f).counit.app P =
        (SingleComplexBaseChange.counit f).app P := by
  let d := schemeHomPullbackCounitData f
  have := d.isLeftDerived
  have := schemeHomCompositionCounit_isLeftDerived f
  simpa only [schemeHomPullbackCounitIso, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso, Iso.refl_hom, NatTrans.id_app, Category.comp_id, id, d] using
    Functor.leftDerivedNatTrans_app (derivedPullback f) (derivedPullback f)
      (SingleComplexBaseChange.counit f) d.counit (HomotopyCategory.quasiIso _ (.up ℤ))
      (𝟙 _) P

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The inverse comparison transports the composition counit back to the original one.
Source: Stacks, Tag 06YJ
(blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomPullbackCounitIso_inv_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :
    (schemeHomPullbackCounitIso f).inv.app (DerivedCategory.Qh.obj P) ≫
      (SingleComplexBaseChange.counit f).app P =
        (schemeHomPullbackCounitData f).counit.app P := by
  rw [← schemeHomPullbackCounitIso_fac f P, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

/-- The canonical tensor comparison is characterized on every pair of K-flat
representatives by the left-derived counits, the localization tensor maps and
termwise module pullback. The degreewise equation pins the chain isomorphism to
the canonical module tensor map on each summand, including its signs.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: lem-pc-global-hom-original-counit-normalization). -/
def IsSchemeHomOriginalCounitTensorComparison {T X : Scheme.{u}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := modulePreadditive X
  letI := modulePreadditive T
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlatTensor → N.IsKFlatTensor →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          cast (by rfl) (((schemeHomPullbackCounitData g).counit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N))) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          cast (by rfl) (((schemeHomPullbackCounitData g).counit).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            ((schemeHomPullbackCounitData g).counit).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The repaired tensor iso satisfies the representative equation with the ORIGINAL counit.
Proof: take the chain comparison in the old canonical predicate. Its summand
formula is unchanged. Precompose its coordinate equation with the change of
presentation, and use naturality to move that change through the localization
map. The counit identities replace all three old counits by the original ones;
the inverse change on the input cancels, giving precisely the transported iso.
Naturality follows from the naturality of the composite natural isomorphism.
Source: Stacks, Tags 06YJ and 079U (blueprint: lem-pc-global-hom-original-counit-normalization). -/
theorem schemeHomOriginalTensorPullbackIso_originalCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSchemeHomOriginalCounitTensorComparison f
      (fun A B ↦ (schemeHomOriginalTensorPullbackIso f).hom.app (A, B)) := by
  have ht := Classical.choose_spec (exists_mixedHomTensorPullbackIso f)
  dsimp only [IsCanonicalPullbackTensorComparison] at ht
  dsimp only [IsSchemeHomOriginalCounitTensorComparison]
  refine ⟨?_, ?_⟩
  · intro P N hP hN
    obtain ⟨φ, hφ, hc⟩ := ht.1 P N hP hN
    refine ⟨φ, hφ, ?_⟩
    have hU := schemeHomPullbackCounitIso_fac f
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Y P N))
    have hA := schemeHomPullbackCounitIso_fac f
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    have hB := schemeHomPullbackCounitIso_fac f
      ((HomotopyCategory.quotient _ (.up ℤ)).obj N)
    have he := originalCounitTensorEquation (derivedPullback f)
      (schemeHomPullbackCounitIso f)
      ((Classical.choose (exists_mixedHomTensorPullbackIso f)).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N))
      (pullbackTensorModelMap Y P N) _ _ _ _ _ _ _ _ hU hA hB hc
    convert he using 1 <;>
      simp only [schemeHomOriginalTensorPullbackIso, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
        NatIso.prod_hom, NatTrans.prod_app_fst, NatTrans.prod_app_snd,
        tensor_obj, tensor_map, Category.assoc] <;> rfl
  · intro A A' B B' a b
    exact (schemeHomOriginalTensorPullbackIso f).hom.naturality
      (X := (A, B)) (Y := (A', B')) (a, b)

attribute [local irreducible] schemeHomOriginalTensorPullbackIso

end AlgebraicGeometry
