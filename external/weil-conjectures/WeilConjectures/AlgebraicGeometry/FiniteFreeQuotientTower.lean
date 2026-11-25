/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

set_option linter.privateModule false

/-! # The basis comparison for the strict tower of quotient complexes

Source: Stacks Project, Modules on Sites, Tags 03CY, 03DA, 03DB and 03EK;
Bhatt--Scholze, Lemma 3.4.12.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid traversing the large dependent tensor transports for tactic style linting.
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules
open scoped ChangeOfRings
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private instance tensorPreadditive (T : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (𝓡 T)) where
  whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
  zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
  whiskerLeft_add := fun {X _Y _Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight := fun {X _Y _Z} f g ↦ (tensorRight X).map_add (f := f) (g := g)

private instance quotientUnitInclusionIso (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    IsIso (koszulTensorUnitInclusion T P) := by
  have (k : ℤ) : IsIso ((koszulTensorUnitInclusion T P).f k) := by
    change IsIso ((λ_ (P.X k)).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso
        (MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T)))
          (SheafOfModules.unit (𝓡 T)) P k).inv)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

@[irreducible] private def quotientUnitIso (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    P ≅ (koszulTensorFunctor T P).obj
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0).obj
        (SheafOfModules.unit (𝓡 T))) :=
  asIso (koszulTensorUnitInclusion T P)

private theorem quotientUnitIso_hom (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    (quotientUnitIso T P).hom = koszulTensorUnitInclusion T P := by
  unfold quotientUnitIso
  rfl

private instance tensorAdditive (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    (koszulTensorFunctor T P).Additive := by
  dsimp only [koszulTensorFunctor]
  infer_instance

private instance tensorColimits (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) :
    PreservesColimitsOfShape WalkingParallelPair (koszulTensorFunctor T P) := by
  let (M : SheafOfModules.{u} (𝓡 T)) :
      PreservesColimitsOfShape WalkingParallelPair
        ((MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T))).flip.obj M) := by
    let : MonoidalClosed (SheafOfModules.{u} (𝓡 T)) := monoidalClosed (R := T)
    let : SymmetricCategory (SheafOfModules.{u} (𝓡 T)) := symmetricCategory T
    change PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorRight M)
    infer_instance
  dsimp only [koszulTensorFunctor]
  infer_instance

@[irreducible] private def unitLeftIso (T : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 T)) :
    ((curriedTensor (SheafOfModules.{u} (𝓡 T))).obj (unit (𝓡 T))).obj M ≅ M :=
  λ_ M

private theorem quotientUnitIso_component (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ) (k : ℤ) :
    (quotientUnitIso T P).hom.f k = (unitLeftIso T (P.X k)).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso
        (curriedTensor (SheafOfModules.{u} (𝓡 T))) (unit (𝓡 T)) P k).inv := by
  rw [quotientUnitIso_hom]
  unfold unitLeftIso
  rfl

private theorem monoidal_counit_leftUnitor
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {X : D} {M : E} (e : F.obj X ≅ M)
    (e₀ : F.obj (𝟙_ D) ≅ 𝟙_ E) (h₀ : e₀.inv = Functor.LaxMonoidal.ε F) :
    (e₀.inv ⊗ₘ e.inv) ≫ Functor.LaxMonoidal.μ F (𝟙_ D) X ≫
      F.map (λ_ X).hom ≫ e.hom = (λ_ M).hom := by
  rw [tensorHom_def', Category.assoc, h₀,
    ← Functor.LaxMonoidal.left_unitality_assoc, leftUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

private theorem tensor_leftUnitor_hom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 R)) :
    let := monoidalCategory R
    let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
    let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
    (tensorObjIsoSheafification (unit (𝓡 R)) M).hom ≫
      S.map (λ_ M.val).hom ≫ ε.app M = (unitLeftIso R M).hom := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
  unfold unitLeftIso
  exact monoidal_counit_leftUnitor S ((asIso ε).app M)
    ((asIso ε).app (unit (𝓡 R))) rfl

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] CategoryTheory.Limits.limit

@[irreducible] private def quotientAction (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) : P ⟶ P :=
  (quotientUnitIso T P).hom ≫ (koszulTensorFunctor T P).map
    ((CochainComplex.singleFunctor (SheafOfModules.{u} (𝓡 T)) 0).map
      (endoPow (globalSectionMultiplication T a) (n + 1))) ≫
        (quotientUnitIso T P).inv

private def transportedCokernel
    {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (G : A ⥤ B) [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair G]
    {X : A} (f : X ⟶ X) [HasCokernel f] {Y : B} (e : Y ≅ G.obj X)
    {g : Y ⟶ Y} (hg : g = e.hom ≫ G.map f ≫ e.inv)
    {q : Y ⟶ G.obj (cokernel f)} (hq : q = e.hom ≫ G.map (cokernel.π f))
    (h : g ≫ q = 0) : IsColimit (CokernelCofork.ofπ q h) := by
  classical
  apply Classical.choice
  constructor
  let hc := isColimitOfHasCokernelOfPreservesColimit G f
  have ht := CokernelCofork.isColimitOfIsColimitOfIff hc g e (by
    intro Z k
    rw [hg, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    constructor
    · intro hk
      rw [hk, comp_zero]
    · intro hk
      apply (cancel_epi e.hom).mp
      simpa only [comp_zero] using hk)
  exact IsColimit.ofIsoColimit ht (Cofork.ext (Iso.refl _) (by simpa using hq.symm))

attribute [local irreducible] transportedCokernel

private theorem singleTensorComponent
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A]
    [Preadditive D] [HasZeroObject D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X : A, (F.obj X).PreservesZeroMorphisms]
    {X : A} (f : X ⟶ X) (P : CochainComplex B ℤ) (k : ℤ) :
    (CochainComplex.mapBifunctorSingle₁XIso F X P k).inv ≫
      (HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P) F (.up ℤ)).f k =
      (F.flip.obj (P.X k)).map f ≫
        (CochainComplex.mapBifunctorSingle₁XIso F X P k).inv := by
  have h := HomologicalComplex.ι_mapBifunctorMap
    ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P) F (.up ℤ)
      0 k k (by simp)
  dsimp only [CochainComplex.mapBifunctorSingle₁XIso]
  simp only [Category.assoc]
  erw [h]
  simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
  let G := F.flip.obj (P.X k)
  have hs : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
      (((HomologicalComplex.single A (.up ℤ) 0).map f).f 0) =
        f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv := by
    rw [HomologicalComplex.single_map_f_self]
    simp
  change G.map _ ≫ G.map _ ≫ _ = G.map _ ≫ G.map _ ≫ _
  exact (G.map_comp_assoc _ _ _).symm.trans
    ((congrArg (fun g ↦ G.map g ≫ _) hs).trans (G.map_comp_assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem unitConjugateComponent
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [(curriedTensor A).PreservesZeroMorphisms]
    [∀ X : A, ((curriedTensor A).obj X).PreservesZeroMorphisms]
    (X : A) (P : CochainComplex A ℤ)
    (l : ∀ k : ℤ, ((curriedTensor A).obj X).obj (P.X k) ≅ P.X k)
    (e : P ≅ HomologicalComplex.mapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj X) P
        (curriedTensor A) (.up ℤ))
    (he : ∀ k, e.hom.f k = (l k).inv ≫
      (CochainComplex.mapBifunctorSingle₁XIso (curriedTensor A) X P k).inv)
    (f : X ⟶ X) (k : ℤ) :
    (e.hom ≫ HomologicalComplex.mapBifunctorMap
      ((HomologicalComplex.single A (.up ℤ) 0).map f) (𝟙 P)
        (curriedTensor A) (.up ℤ) ≫ e.inv).f k =
      (l k).inv ≫ ((curriedTensor A).flip.obj (P.X k)).map f ≫
        (l k).hom := by
  let b := CochainComplex.mapBifunctorSingle₁XIso (curriedTensor A) X P k
  have hi : (HomologicalComplex.eval A (.up ℤ) k).mapIso e =
      (l k).symm ≪≫ b.symm := Iso.ext (he k)
  have hh := congrArg Iso.hom hi
  have hv := congrArg Iso.inv hi
  simp only [HomologicalComplex.comp_f]
  rw [show e.hom.f k = (l k).inv ≫ b.inv from hh,
    show e.inv.f k = b.hom ≫ (l k).hom from hv]
  have h := singleTensorComponent (curriedTensor A) f P k
  change b.inv ≫ _ = ((curriedTensor A).flip.obj (P.X k)).map f ≫ b.inv at h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun g ↦ (l k).inv ≫ g ≫ b.hom ≫ (l k).hom) h

private theorem quotientAction_component (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) (k : ℤ) :
    (quotientAction T P a n).f k =
      (unitLeftIso T (P.X k)).inv ≫
        ((MonoidalCategory.curriedTensor (SheafOfModules.{u} (𝓡 T))).flip.obj
          (P.X k)).map (endoPow (globalSectionMultiplication T a) (n + 1)) ≫
            (unitLeftIso T (P.X k)).hom := by
  unfold quotientAction
  exact unitConjugateComponent (unit (𝓡 T)) P (fun k ↦ unitLeftIso T (P.X k))
    (quotientUnitIso T P) (quotientUnitIso_component T P)
    (endoPow (globalSectionMultiplication T a) (n + 1)) k

attribute [local irreducible] koszulTensorFunctor

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionScalar
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (𝓡 R)).sections) :
    𝟭 (SheafOfModules.{u} (𝓡 R)) ⟶ 𝟭 _ where
  app M :=
    ⟨{ app := fun U => ModuleCat.ofHom
          (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (s.val U))
       naturality := by
         intro U V i
         apply ModuleCat.hom_ext
         apply LinearMap.ext
         intro x
         change (show R.obj.obj V from s.val V) • (show M.val.obj V from M.val.map i x) =
           M.val.map i ((show R.obj.obj U from s.val U) • x)
         rw [M.val.map_smul]
         exact congrArg (fun a : R.obj.obj V ↦ a • (show M.val.obj V from M.val.map i x))
           (s.property i).symm }⟩
  naturality {M N} a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((a.val.app U).hom.map_smul (s.val U) x).symm

private theorem transportedSquare
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (a : X' ⟶ F.obj X) (b : F.obj Y ⟶ Y')
    (f : X' ⟶ X') (g : X ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Y) (l : Y' ⟶ Y')
    (ha : f ≫ a = a ≫ F.map g) (hpre : g ≫ h = h ≫ k)
    (hb : F.map k ≫ b = b ≫ l) :
    f ≫ (a ≫ F.map h ≫ b) = (a ≫ F.map h ≫ b) ≫ l := by
  rw [← Category.assoc, ha, Category.assoc, ← F.map_comp_assoc,
    hpre, F.map_comp, Category.assoc, hb]
  simp only [Category.assoc]

private theorem scalar_leftUnitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (𝓡 R)).sections)
    (M : SheafOfModules.{u} (𝓡 R)) :
    letI := monoidalCategory R
    globalSectionMultiplication R s ▷ M ≫ (unitLeftIso R M).hom =
      (unitLeftIso R M).hom ≫ (sectionScalar R s).app M := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification.{u} (𝟙 (𝓡 R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡 R).obj)).counit
  have hpre : (globalSectionMultiplication R s).val ▷ M.val ≫ (λ_ M.val).hom =
      (λ_ M.val).hom ≫ ((sectionScalar R s).app M).val := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    change R.obj.obj V at a
    change (a * (show R.obj.obj V from s.val V)) • x =
      (show R.obj.obj V from s.val V) • (a • x)
    rw [mul_smul, smul_comm]
  have hε := ε.naturality ((sectionScalar R s).app M)
  change S.map ((sectionScalar R s).app M).val ≫ ε.app M =
    ε.app M ≫ (sectionScalar R s).app M at hε
  have h := transportedSquare S
    (tensorObjIsoSheafification (unit (𝓡 R)) M).hom (ε.app M)
    (globalSectionMultiplication R s ▷ M)
    ((globalSectionMultiplication R s).val ▷ M.val) (λ_ M.val).hom
    ((sectionScalar R s).app M).val ((sectionScalar R s).app M)
    (whiskerRight_tensorObjIsoSheafification_hom (R := R)
      (globalSectionMultiplication R s) M) hpre hε
  exact (congrArg (globalSectionMultiplication R s ▷ M ≫ ·)
    (tensor_leftUnitor_hom R M)).symm.trans
      (h.trans (congrArg (· ≫ (sectionScalar R s).app M) (tensor_leftUnitor_hom R M)))

private theorem conjugatedMapPow
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {X : A} {Y : B} (e : Y ≅ F.obj X) (f : X ⟶ X) (m : ℕ) :
    e.hom ≫ F.map (endoPow f m) ≫ e.inv =
      endoPow (e.hom ≫ F.map f ≫ e.inv) m := by
  induction m with
  | zero => simp only [endoPow, Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  | succ m ih =>
    simp only [endoPow, Functor.map_comp]
    rw [← ih]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem quotientAction_apply (T : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u} (𝓡 T)) ℤ)
    (a : (SheafOfModules.unit (𝓡 T)).sections) (n : ℕ) (k : ℤ) (V : Cᵒᵖ)
    (x : (P.X k).val.obj V) :
    ((quotientAction T P a n).f k).val.app V x =
      (show T.obj.obj V from a.val V) ^ (n + 1) • x := by
  let G := (MonoidalCategory.curriedTensor
    (SheafOfModules.{u} (𝓡 T))).flip.obj (P.X k)
  have hbase : (unitLeftIso T (P.X k)).inv ≫ G.map (globalSectionMultiplication T a) ≫
      (unitLeftIso T (P.X k)).hom = (sectionScalar T a).app (P.X k) := by
    exact (congrArg ((unitLeftIso T (P.X k)).inv ≫ ·) (scalar_leftUnitor T a (P.X k))).trans
      (by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp])
  have hp (m : ℕ) :
      ((endoPow ((sectionScalar T a).app (P.X k)) m).val.app V) x =
        (show T.obj.obj V from a.val V) ^ m • x := by
    induction m with
    | zero => change x = _; simp
    | succ m ih =>
      change (show T.obj.obj V from a.val V) •
        ((endoPow ((sectionScalar T a).app (P.X k)) m).val.app V x) = _
      rw [ih, pow_succ, mul_smul, smul_comm]
  rw [quotientAction_component]
  change (( (unitLeftIso T (P.X k)).inv ≫ G.map
    (endoPow (globalSectionMultiplication T a) (n + 1)) ≫
      (unitLeftIso T (P.X k)).hom).val.app V) x = _
  have hpow : (unitLeftIso T (P.X k)).inv ≫ G.map
      (endoPow (globalSectionMultiplication T a) (n + 1)) ≫ (unitLeftIso T (P.X k)).hom =
        endoPow ((sectionScalar T a).app (P.X k)) (n + 1) :=
    (conjugatedMapPow G (unitLeftIso T (P.X k)).symm
      (globalSectionMultiplication T a) (n + 1)).trans
        (congrArg (fun f ↦ endoPow f (n + 1)) hbase)
  exact (congrArg (fun f ↦ (f.val.app V) x) hpow).trans (hp (n + 1))

private instance mapComplexColimits {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasColimitsOfShape WalkingParallelPair A]
    [HasColimitsOfShape WalkingParallelPair B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    PreservesColimitsOfShape WalkingParallelPair (F.mapHomologicalComplex (.up ℤ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro k
  change PreservesColimitsOfShape WalkingParallelPair
    (HomologicalComplex.eval A (.up ℤ) k ⋙ F)
  infer_instance

attribute [local irreducible] reductionTensorTower
  koszulRepresentativeQuotient

private instance whiskerPreservesZero
    {I A B : Type*} [Category* I] [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] :
    ((Functor.whiskeringRight I A B).obj F).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i
    exact F.map_zero (X.obj i) (Y.obj i)

end CategoryTheory
