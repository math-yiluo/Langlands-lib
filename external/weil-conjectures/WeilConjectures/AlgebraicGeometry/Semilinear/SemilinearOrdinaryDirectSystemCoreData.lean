/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectRestrictions
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import WeilConjectures.AlgebraicGeometry.OrdinarySource.SemilinearOrdinarySourceStrictSystem

/-! # Reassembly of the ordinary direct image

## References

* Zheng Construction 4.1
* Stacks 03D2 and 03DA
* Stacks 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

attribute [local irreducible] evaluation transition

variable (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
  (a : ∀ n, (I n).modules ⊣ V n)

/-- The componentwise data of a direct-system core, before the mate condition.

This records only the functor and its levelwise component identifications.  The
transition mate law is stated separately, since it is a local assertion about
two component maps and is independent of the reassembly of system morphisms. -/
structure OrdinaryDirectSystemCoreData
    (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
    (J' : GrothendieckTopology C')
    (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
    (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
    where
  push : Systems.{c, v, max c v r} J' F σ ⥤ Systems.{c, v, max c v r} J B τ
  component : ∀ n,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{c, v, max c v r} J' F σ n ⋙ V n
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J' F σ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x

/-- The horizontal maps of a component datum are the supplied set-sheaf direct images. -/
def OrdinaryDirectSystemCoreNormalized
    (D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush) : Prop :=
  ∀ (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m),
    (underlying.{c, v, r} J (B m)).map
        ((transition.{c, v, max c v r} J B τ h).app (D.push.obj N)) ≫
      (underlying.{c, v, r} J (B n)).map ((D.component n).hom.app N) ≫
      (eV n).hom.app ((evaluation.{c, v, max c v r} J' F σ n).obj N) =
    (underlying.{c, v, r} J (B m)).map ((D.component m).hom.app N) ≫
      (eV m).hom.app ((evaluation.{c, v, max c v r} J' F σ m).obj N) ≫
      uPush.map ((underlying.{c, v, r} J' (F m)).map
        ((transition.{c, v, max c v r} J' F σ h).app N))

private def directStrictTransition
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ))
    {m n : ℕ} (h : m ≤ n) :
    (V n).obj (M.level n) ⟶ (res (coefficientMap J B τ h)).obj ((V m).obj (M.level m)) :=
  (V n).map (M.transition h) ≫ (δ.iso h).hom.app (M.level m)

private theorem directStrictTransition_normalized
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ))
    {m n : ℕ} (h : m ≤ n) :
    (underlying.{c, v, r} J (B n)).map
        (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M h) ≫
      (eV m).hom.app (M.level m) =
      (eV n).hom.app (M.level n) ≫
        uPush.map ((underlying.{c, v, r} J' (F n)).map (M.transition h)) := by
  calc
    _ = (underlying.{c, v, r} J (B n)).map ((V n).map (M.transition h)) ≫
        ((underlying.{c, v, r} J (B n)).map ((δ.iso h).hom.app (M.level m)) ≫
          (eV m).hom.app (M.level m)) := by
      simp only [directStrictTransition, Functor.map_comp, Category.assoc]
    _ = (underlying.{c, v, r} J (B n)).map ((V n).map (M.transition h)) ≫
        (eV n).hom.app ((res (coefficientMap J' F σ h)).obj (M.level m)) :=
      congrArg ((underlying.{c, v, r} J (B n)).map
        ((V n).map (M.transition h)) ≫ ·) (δ.normalized h (M.level m))
    _ = _ := (eV n).hom.naturality (M.transition h)

private theorem directStrictTransition_underlying
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ))
    {m n : ℕ} (h : m ≤ n) :
    (underlying.{c, v, r} J (B n)).map
        (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M h) =
      (eV n).hom.app (M.level n) ≫
        uPush.map ((underlying.{c, v, r} J' (F n)).map (M.transition h)) ≫
        (eV m).inv.app (M.level m) := by
  apply (cancel_mono ((eV m).hom.app (M.level m))).1
  exact (directStrictTransition_normalized.{c, v, r} J B τ J' F σ V uPush eV δ M h).trans
    (by
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm)

private def directStrictUnderlying
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ)) :
    ℕᵒᵖ ⥤ Sheaf J' (Type (max c v r)) where
  obj n := (underlying.{c, v, r} J' (F n.unop)).obj (M.level n.unop)
  map f := (underlying.{c, v, r} J' (F _)).map (M.transition (leOfHom f.unop))
  map_id n := by
    ext U x
    exact M.identity n.unop U x
  map_comp f g := by
    ext U x
    exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x

private theorem directStrict_identity
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ))
    (n : ℕ) (U : Cᵒᵖ) (x : ((V n).obj (M.level n)).val.obj U) :
    (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M
      (Nat.le_refl n)).val.app U x = x := by
  have he := directStrictTransition_underlying.{c, v, r} J B τ J' F σ V uPush eV δ M
    (Nat.le_refl n)
  change _ = (eV n).hom.app _ ≫
    uPush.map ((directStrictUnderlying.{c, v, r} J' F σ M).map (𝟙 (op n))) ≫ _ at he
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app] at he
  exact congrArg (fun f ↦ f.hom.app U x) he

private theorem conjugate_map_comp
    {A D : Type*} [Category A] [Category D] (F : A ⥤ D)
    {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
    {X Y Z : D} (p : X ≅ F.obj a) (q : Y ≅ F.obj b) (r : Z ≅ F.obj c) :
    p.hom ≫ F.map (f ≫ g) ≫ r.inv =
      (p.hom ≫ F.map f ≫ q.inv) ≫ (q.hom ≫ F.map g ≫ r.inv) := by
  simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

private theorem directStrict_compose
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ))
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (U : Cᵒᵖ)
    (x : ((V n).obj (M.level n)).val.obj U) :
    (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M (h.trans k)).val.app U x =
      (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M h).val.app U
        ((directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M k).val.app U x) := by
  let d := directStrictUnderlying.{c, v, r} J' F σ M ⋙ uPush
  have he₁ := directStrictTransition_underlying.{c, v, r} J B τ J' F σ V uPush eV δ M
    (h.trans k)
  have he₂ := directStrictTransition_underlying.{c, v, r} J B τ J' F σ V uPush eV δ M k
  have he₃ := directStrictTransition_underlying.{c, v, r} J B τ J' F σ V uPush eV δ M h
  have hc := conjugate_map_comp d (homOfLE k).op (homOfLE h).op
    ((eV n).app (M.level n)) ((eV m).app (M.level m)) ((eV l).app (M.level l))
  have he := he₁.trans (hc.trans (congrArg₂ (· ≫ ·) he₂.symm he₃.symm))
  exact congrArg (fun f ↦ f.hom.app U x) he

private def directStrictObject
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ)) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  level n := (V n).obj (M.level n)
  transition h := directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M h
  identity := directStrict_identity.{c, v, r} J B τ J' F σ V uPush eV δ M
  compose := directStrict_compose.{c, v, r} J B τ J' F σ V uPush eV δ M

private theorem directStrictMap_comm
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    {M N : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ)}
    (f : M ⟶ N) {m n : ℕ} (h : m ≤ n) :
    (V n).map (f.app n) ≫
        directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ N h =
      directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ M h ≫
        (res (coefficientMap J B τ h)).map ((V m).map (f.app m)) := by
  dsimp only [directStrictTransition]
  erw [← Category.assoc, ← Functor.map_comp, f.comm h, Functor.map_comp, Category.assoc]
  exact congrArg ((V n).map (M.transition h) ≫ ·) ((δ.iso h).hom.naturality (f.app m))

private def directStrictFunctor
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ) ⥤
      SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  obj := directStrictObject.{c, v, r} J B τ J' F σ V uPush eV δ
  map f :=
    { app := fun n ↦ (V n).map (f.app n)
      comm := directStrictMap_comm.{c, v, r} J B τ J' F σ V uPush eV δ f }
  map_id M := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (V n).map_id _
  map_comp f g := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (V n).map_comp _ _

section DirectReassembly
attribute [local semireducible] evaluation transition

private theorem directEvaluationRingMap (n : ℕ) :
    eqToHom (evaluation_ring J B τ n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (rings J B τ) n := by
  ext U x
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def directSequenceLevelIso
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ)) (n : ℕ) :
    (evaluation J B τ n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) ≅
        M.level n :=
  (SheafOfModules.pushforwardCongr (directEvaluationRingMap.{c, v, r} J B τ n)).app
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) ≪≫
    (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ) M n).symm

private theorem directSequenceLevelIso_sections
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    (n : ℕ) (U : Cᵒᵖ)
    (x : ((evaluation J B τ n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M)).val.obj U) :
    HEq (((directSequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U) x) x := by
  rfl

private theorem directSequenceTransition
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : (M.level m).val.obj U) :
    ((res (coefficientMap J B τ h)).map (directSequenceLevelIso.{c, v, r} J B τ M n).hom).val.app U
      (((transition J B τ h).app
        ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M)).val.app U
          ((directSequenceLevelIso.{c, v, r} J B τ M m).inv.val.app U x)) =
      (M.transition h).val.app U x := by
  have hh := (transition_exists J B τ h).exists.choose_spec
    ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) U
  have he := congrFun (eq_of_heq hh) ((directSequenceLevelIso.{c, v, r} J B τ M m).inv.val.app U x)
  change (directSequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U _ = _
  refine (congrArg ((directSequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U) he).trans ?_
  change (M.level n).val.map (𝟙 U) ((M.transition h).val.app U x) = _
  erw [PresheafOfModules.map_id]
  rfl

private theorem underlyingRestrictionMap
    {R R' : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ R')
    {M N : Mod.{c, v, max c v r} J R'} (f : M ⟶ N) :
    (underlying.{c, v, r} J R).map ((res φ).map f) =
      (underlying.{c, v, r} J R').map f := by
  rfl

private theorem paste_normalized_squares
    {A : Type*} [Category A] {W X Y Z T S : A}
    (f : W ⟶ X) (g : X ⟶ Y) (i : W ⟶ Z) (j : Z ⟶ Y)
    (k : Y ⟶ T) (l : Z ⟶ S) (m : S ⟶ T)
    (hf : f ≫ g = i ≫ j) (hj : j ≫ k = l ≫ m) :
    f ≫ g ≫ k = i ≫ l ≫ m := by
  rw [← Category.assoc, hf, Category.assoc, hj]

section NormalizationProof
attribute [local irreducible] evaluation transition directStrictTransition

private theorem core_normalized_of_transition
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (δ : DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV)
    (D : OrdinaryDirectSystemCoreData.{c, v, r} J B τ J' F σ V)
    (hT : ∀ (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m),
      (transition J B τ h).app (D.push.obj N) ≫
        (res (coefficientMap J B τ h)).map ((D.component n).hom.app N) =
      (D.component m).hom.app N ≫
        directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ
          ((OrdinarySource.sourceStrictFunctor.{c, v, r} J' F σ).obj N) h) :
    OrdinaryDirectSystemCoreNormalized.{c, v, r} J B τ J' F σ V D uPush eV := by
  intro N m n h
  have he' := congrArg ((underlying.{c, v, r} J (B m)).map) (hT N h)
  simp only [Functor.map_comp, underlyingRestrictionMap] at he'
  have hn := directStrictTransition_normalized.{c, v, r} J B τ J' F σ V uPush eV δ
    ((OrdinarySource.sourceStrictFunctor.{c, v, r} J' F σ).obj N) h
  let f := (underlying.{c, v, r} J (B m)).map
    ((transition J B τ h).app (D.push.obj N))
  let g := (underlying.{c, v, r} J (B n)).map ((D.component n).hom.app N)
  let i := (underlying.{c, v, r} J (B m)).map ((D.component m).hom.app N)
  let j := (underlying.{c, v, r} J (B m)).map
    (directStrictTransition.{c, v, r} J B τ J' F σ V uPush eV δ
      ((OrdinarySource.sourceStrictFunctor.{c, v, r} J' F σ).obj N) h)
  let k := (eV n).hom.app ((evaluation J' F σ n).obj N)
  let l := (eV m).hom.app ((evaluation J' F σ m).obj N)
  let q := uPush.map ((underlying.{c, v, r} J' (F m)).map ((transition J' F σ h).app N))
  exact paste_normalized_squares f g i j k l q he' hn

end NormalizationProof

attribute [local irreducible] transition directStrictTransition

/-- Reassemble the componentwise direct-image datum. -/
theorem ordinaryDirectSystem_core_data_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    ∃ D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
        (J' := J') (F := F) (σ := σ) (V := V),
      OrdinaryDirectSystemCoreNormalized.{c, v, r} J B τ J' F σ V D uPush eV := by
  classical
  obtain ⟨δ⟩ := directRestrictions_exists.{c, v, r} J B τ J' uInv F σ I V a
    hI uPush adjSet eV ha
  let G := OrdinarySource.sourceStrictFunctor.{c, v, r} J' F σ ⋙
    directStrictFunctor.{c, v, r} J B τ J' F σ V uPush eV δ
  let push := G ⋙ (SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor
  let component : ∀ n, push ⋙ evaluation J B τ n ≅
      evaluation J' F σ n ⋙ V n := fun n ↦
    NatIso.ofComponents
      (fun N ↦ directSequenceLevelIso.{c, v, r} J B τ (G.obj N) n)
      (by intros; ext U x; rfl)
  let D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V) :=
    { push := push
      component := component
      component_sections := fun n N U x ↦
        directSequenceLevelIso_sections.{c, v, r} J B τ (G.obj N) n U x }
  refine ⟨D, core_normalized_of_transition.{c, v, r} J B τ J' F σ V
    uPush eV δ D ?_⟩
  intro N m n h
  apply (cancel_epi ((component m).inv.app N)).1
  simp only [← Category.assoc]
  ext U x
  exact directSequenceTransition.{c, v, r} J B τ (G.obj N) h U x

end DirectReassembly

end WeilConjectures.SemilinearSections
end
