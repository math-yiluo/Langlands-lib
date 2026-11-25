/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison
import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.AlgebraicGeometry.OrdinarySource.SemilinearOrdinarySourceStrictSystem

/-! # Ordinary inverse image on the ringed sequence site

## References

* Zheng Construction 4.1
* Stacks 03D2 and 03DA
* Zheng Construction 4.1, paragraph before Lemma 4.10
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

/-- Only the inverse-image part of the ordinary system construction. -/
structure OrdinaryInverseSystem where
  pull : Systems.{c, v, max c v r} J B τ ⥤ Systems.{c, v, max c v r} J' F σ
  [limits : PreservesFiniteLimits pull]
  [colimits : PreservesFiniteColimits pull]
  component : ∀ n,
    pull ⋙ evaluation.{c, v, max c v r} J' F σ n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙ (I n).modules
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J B τ) (U : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' F σ n).obj (pull.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x
  restriction : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) ⋙ (I m).modules ≅
      (I n).modules ⋙ res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)
  restriction_underlying : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (F m)).map ((restriction h).hom.app M) ≫
      (I n).moduleUnderlying.hom.app M =
        (I m).moduleUnderlying.hom.app
          ((res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).obj M)
  transition : ∀ {m n : ℕ} (h : n ≤ m) (M : Systems.{c, v, max c v r} J B τ),
    (transition.{c, v, max c v r} J' F σ h).app (pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)).map
          ((component n).hom.app M) =
      (component m).hom.app M ≫
        (I m).modules.map ((transition.{c, v, max c v r} J B τ h).app M) ≫
        (restriction h).hom.app ((evaluation.{c, v, max c v r} J B τ n).obj M)

attribute [instance] OrdinaryInverseSystem.limits OrdinaryInverseSystem.colimits

-- Scalar comparisons are normalized on underlying sheaves.
private structure InverseRestrictions where
  iso : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap J B τ h) ⋙ (I m).modules ≅
      (I n).modules ⋙ res.{c, v, max c v r} (coefficientMap J' F σ h)
  normalized : ∀ {m n : ℕ} (h : n ≤ m) (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (F m)).map ((iso h).hom.app M) ≫
      (I n).moduleUnderlying.hom.app M =
        (I m).moduleUnderlying.hom.app ((res (coefficientMap J B τ h)).obj M)

private theorem inverseRestrictions_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n)) :
    Nonempty (InverseRestrictions.{c, v, r} J B τ J' uInv F σ I) := by
  classical
  let α : rings J B τ ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r}) ⋙
      uInv ⟶ rings J' F σ ⋙
        sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r}) :=
    NatTrans.ofOpSequence (fun n ↦ (I n).ringUnderlying.hom) (by
      intro n
      simpa only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ]
        using hI n)
  have hc {m n : ℕ} (h : n ≤ m) :
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map
          (coefficientMap J B τ h)) ≫ (I n).ringUnderlying.hom =
        (I m).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map
            (coefficientMap J' F σ h) := α.naturality (homOfLE h).op
  have hρ {m n : ℕ} (h : n ≤ m) :=
    SheafOfModules.InverseImageScalarRestriction.exists_comparison
      (I m) (I n) (coefficientMap J B τ h) (coefficientMap J' F σ h) (hc h)
  refine ⟨{ iso := fun h ↦ (hρ h).choose.symm, normalized := ?_ }⟩
  intro m n h M
  have he := (hρ h).choose_spec M
  change (underlying.{c, v, r} J' (F m)).map ((hρ h).choose.inv.app M) ≫
    (I n).moduleUnderlying.hom.app M = _
  rw [← he, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private def inverseStrictTransition
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    {m n : ℕ} (h : m ≤ n) :
    (I n).modules.obj (M.level n) ⟶
      (res (coefficientMap J' F σ h)).obj ((I m).modules.obj (M.level m)) :=
  (I n).modules.map (M.transition h) ≫ (ρ.iso h).hom.app (M.level m)

private theorem inverseStrictTransition_underlying
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    {m n : ℕ} (h : m ≤ n) :
    (underlying.{c, v, r} J' (F n)).map
        (X := (I n).modules.obj (M.level n))
        (Y := (res (coefficientMap J' F σ h)).obj ((I m).modules.obj (M.level m)))
        (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M h) =
      (I n).moduleUnderlying.hom.app (M.level n) ≫
        uInv.map ((underlying.{c, v, r} J (B n)).map (M.transition h)) ≫
        (I m).moduleUnderlying.inv.app (M.level m) := by
  apply (cancel_mono ((I m).moduleUnderlying.hom.app (M.level m))).1
  simp only [inverseStrictTransition, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  rw [ρ.normalized]
  exact (I n).moduleUnderlying.hom.naturality (M.transition h)

private def strictUnderlying
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ)) :
    ℕᵒᵖ ⥤ Sheaf J (Type (max c v r)) where
  obj n := (underlying.{c, v, r} J (B n.unop)).obj (M.level n.unop)
  map f := (underlying.{c, v, r} J (B _)).map (M.transition (leOfHom f.unop))
  map_id n := by
    ext U x
    exact M.identity n.unop U x
  map_comp f g := by
    ext U x
    exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x

private theorem inverseStrict_identity
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    (n : ℕ) (U : C'ᵒᵖ) (x : ((I n).modules.obj (M.level n)).val.obj U) :
    (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M (Nat.le_refl n)).val.app U x =
      x := by
  have he := inverseStrictTransition_underlying.{c, v, r} J B τ J' uInv F σ I ρ M
    (Nat.le_refl n)
  change _ = (I n).moduleUnderlying.hom.app _ ≫
    uInv.map ((strictUnderlying.{c, v, r} J B τ M).map (𝟙 (op n))) ≫ _ at he
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app] at he
  exact congrArg (fun f ↦ f.hom.app U x) he

private theorem inverseStrict_compose
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (U : C'ᵒᵖ) (x : ((I n).modules.obj (M.level n)).val.obj U) :
    (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M (h.trans k)).val.app U x =
      (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M h).val.app U
        ((inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M k).val.app U x) := by
  let d := strictUnderlying.{c, v, r} J B τ M ⋙ uInv
  have he : (underlying.{c, v, r} J' (F n)).map
      (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M (h.trans k)) =
      (underlying.{c, v, r} J' (F n)).map
        (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M k) ≫
      (underlying.{c, v, r} J' (F m)).map
        (inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M h) := by
    rw [inverseStrictTransition_underlying, inverseStrictTransition_underlying,
      inverseStrictTransition_underlying]
    change (I n).moduleUnderlying.hom.app _ ≫ d.map (homOfLE (h.trans k)).op ≫ _ =
      ((I n).moduleUnderlying.hom.app _ ≫ d.map (homOfLE k).op ≫
        (I m).moduleUnderlying.inv.app _) ≫
      (I m).moduleUnderlying.hom.app _ ≫ d.map (homOfLE h).op ≫ _
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc]
    rfl
  exact congrArg (fun f ↦ f.hom.app U x) he

private def inverseStrictObject
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ)) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ) where
  level n := (I n).modules.obj (M.level n)
  transition h := inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M h
  identity := inverseStrict_identity.{c, v, r} J B τ J' uInv F σ I ρ M
  compose := inverseStrict_compose.{c, v, r} J B τ J' uInv F σ I ρ M

private theorem inverseStrictMap_comm
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I)
    {M N : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ)}
    (f : M ⟶ N) {m n : ℕ} (h : m ≤ n) :
    (I n).modules.map (f.app n) ≫
        inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ N h =
      inverseStrictTransition.{c, v, r} J B τ J' uInv F σ I ρ M h ≫
        (res (coefficientMap J' F σ h)).map ((I m).modules.map (f.app m)) := by
  dsimp only [inverseStrictTransition]
  rw [← Category.assoc, ← Functor.map_comp, f.comm h, Functor.map_comp, Category.assoc]
  exact congrArg ((I n).modules.map (M.transition h) ≫ ·)
    ((ρ.iso h).hom.naturality (f.app m))

private def inverseStrictFunctor
    (ρ : InverseRestrictions.{c, v, r} J B τ J' uInv F σ I) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) ⥤
      SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J' F σ) where
  obj := inverseStrictObject.{c, v, r} J B τ J' uInv F σ I ρ
  map f :=
    { app := fun n ↦ (I n).modules.map (f.app n)
      comm := inverseStrictMap_comm.{c, v, r} J B τ J' uInv F σ I ρ f }
  map_id M := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (I n).modules.map_id _
  map_comp f g := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (I n).modules.map_comp _ _

private theorem evaluationRingMap (n : ℕ) :
    eqToHom (evaluation_ring J B τ n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (rings J B τ) n := by
  ext U x
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def sequenceLevelIso
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ)) (n : ℕ) :
    (evaluation J B τ n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) ≅
        M.level n :=
  (SheafOfModules.pushforwardCongr (evaluationRingMap.{c, v, r} J B τ n)).app
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) ≪≫
    (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ) M n).symm

private theorem sequenceLevelIso_sections
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    (n : ℕ) (U : Cᵒᵖ)
    (x : ((evaluation J B τ n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M)).val.obj U) :
    HEq (((sequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U) x) x := by
  rfl

private theorem sequenceTransition
    (M : SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : (M.level m).val.obj U) :
    ((res (coefficientMap J B τ h)).map (sequenceLevelIso.{c, v, r} J B τ M n).hom).val.app U
      (((transition J B τ h).app
        ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M)).val.app U
          ((sequenceLevelIso.{c, v, r} J B τ M m).inv.val.app U x)) =
      (M.transition h).val.app U x := by
  have hh := (transition_exists J B τ h).exists.choose_spec
    ((SheafOfModules.strictSystemSequenceEquivalence (rings J B τ)).functor.obj M) U
  have he := congrFun (eq_of_heq hh) ((sequenceLevelIso.{c, v, r} J B τ M m).inv.val.app U x)
  change (sequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U _ = _
  refine (congrArg ((sequenceLevelIso.{c, v, r} J B τ M n).hom.val.app U) he).trans ?_
  change (M.level n).val.map (𝟙 U) ((M.transition h).val.app U x) = _
  rw [PresheafOfModules.map_id]
  rfl

private theorem strictFunctor_exact {A : Type*} [Category A]
    [HasFiniteLimits A] [HasFiniteColimits A]
    (G : A ⥤ SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ))
    [∀ n, PreservesFiniteLimits (G ⋙ SheafOfModules.systemEvaluation (rings J B τ) n)]
    [∀ n, PreservesFiniteColimits (G ⋙ SheafOfModules.systemEvaluation (rings J B τ) n)] :
    PreservesFiniteLimits G ∧ PreservesFiniteColimits G := by
  let E := fun n : ℕ ↦ SheafOfModules.systemEvaluation.{c, v, max c v r} (rings J B τ) n
  have hE : JointlyReflectIsomorphisms E :=
    { isIso f := (SheafOfModules.strictRingSystem_isIso_iff (rings J B τ) f).2
        (fun n ↦ inferInstance) }
  constructor
  · constructor
    intro K _ _
    constructor
    intro D
    constructor
    intro c hc
    refine ⟨hE.jointlyReflectsLimit (fun n ↦ ?_)⟩
    exact isLimitOfPreserves (G ⋙ E n) hc
  · constructor
    intro K _ _
    constructor
    intro D
    constructor
    intro c hc
    refine ⟨hE.jointlyReflectsColimit (fun n ↦ ?_)⟩
    exact isColimitOfPreserves (G ⋙ E n) hc

/-- Termwise inverse image, with its actual horizontal maps, can be assembled on the
ringed sequence site. No direct image or adjunction is asserted. -/
theorem ordinaryInverseSystem_exists [PreservesFiniteLimits uInv]
    [∀ n, PreservesFiniteLimits (I n).modules]
    [∀ n, PreservesFiniteColimits (I n).modules]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n)) :
    Nonempty (OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I) := by
  classical
  obtain ⟨ρ⟩ := inverseRestrictions_exists.{c, v, r} J B τ J' uInv F σ I hI
  let G := OrdinarySource.sourceStrictFunctor.{c, v, r} J B τ ⋙
    inverseStrictFunctor.{c, v, r} J B τ J' uInv F σ I ρ
  have hGl (n : ℕ) : PreservesFiniteLimits
      (G ⋙ SheafOfModules.systemEvaluation (rings J' F σ) n) := by
    change PreservesFiniteLimits (evaluation J B τ n ⋙ (I n).modules)
    infer_instance
  have hGc (n : ℕ) : PreservesFiniteColimits
      (G ⋙ SheafOfModules.systemEvaluation (rings J' F σ) n) := by
    change PreservesFiniteColimits (evaluation J B τ n ⋙ (I n).modules)
    infer_instance
  obtain ⟨hl, hc⟩ := strictFunctor_exact.{c, v, r} J' F σ G
  let pull := G ⋙ (SheafOfModules.strictSystemSequenceEquivalence (rings J' F σ)).functor
  let component : ∀ n, pull ⋙ evaluation J' F σ n ≅
      evaluation J B τ n ⋙ (I n).modules := fun n ↦
    NatIso.ofComponents
      (fun M ↦ sequenceLevelIso.{c, v, r} J' F σ (G.obj M) n)
      (by intros; ext U x; rfl)
  refine ⟨{
    pull := pull
    limits := ?_
    colimits := ?_
    component := component
    component_sections := ?_
    restriction := ρ.iso
    restriction_underlying := ρ.normalized
    transition := ?_ }⟩
  · infer_instance
  · infer_instance
  · intro n M U x
    exact sequenceLevelIso_sections.{c, v, r} J' F σ (G.obj M) n U x
  · intro m n h M
    apply (cancel_epi ((component m).inv.app M)).1
    simp only [← Category.assoc, Iso.inv_hom_id_app]
    ext U x
    exact sequenceTransition.{c, v, r} J' F σ (G.obj M) h U x

end WeilConjectures.SemilinearSections

end
