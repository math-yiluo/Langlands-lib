/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite

/-! # Constant sequence modules with independent site universes

Source: Stacks Project, Tags 03DA and 0940; Zheng, Construction 4.1
(blueprint: def-coef-constant-sequence-equivalence).
The forward and inverse functors are constructed from strict systems, not chosen
from an existence theorem. The proved same-universe dependency is unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace CategoryTheory.ConstantCompletion

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

/-- The independentSystem construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
abbrev independentSystem :=
  SheafOfModules.StrictRingSystem.{c, v, max c v r} (J := J) ((Functor.const ℕᵒᵖ).obj O)

/-- The independentToTower construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentToTower : independentSystem.{c, v, r} O ⥤ (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r}
        ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) where
  obj M :=
    { obj n := M.level n.unop
      map h := M.transition (leOfHom h.unop)
      map_id n := by
        ext U x
        exact M.identity n.unop U x
      map_comp f g := by
        ext U x
        exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x }
  map f :=
    { app n := f.app n.unop
      naturality := by
        intro n m h
        exact (f.comm (leOfHom h.unop)).symm }
  map_id M := rfl
  map_comp f g := rfl

/-- The independentFromTower construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentFromTower : (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ⥤ independentSystem.{c, v,
        r} O where
  obj F :=
    { level n := F.obj (op n)
      transition h := F.map (homOfLE h).op
      identity n U x := by
        have h := congrArg (fun f ↦ f.val.app U) (F.map_id (op n))
        exact ConcreteCategory.congr_hom h x
      compose h k U x := by
        have h := congrArg (fun f ↦ f.val.app U)
          (F.map_comp (homOfLE k).op (homOfLE h).op)
        exact ConcreteCategory.congr_hom h x }
  map f :=
    { app n := f.app (op n)
      comm := by
        intro n m h
        exact (f.naturality (homOfLE h).op).symm }
  map_id F := rfl
  map_comp f g := rfl

-- Identity coefficient restrictions require reducing the varying-ring system interface.
/-- The independentSystemTowerEquivalence construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentSystemTowerEquivalence : independentSystem.{c, v, r} O ≌
    (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) where
  functor := independentToTower.{c, v, r} O
  inverse := independentFromTower.{c, v, r} O
  unitIso := NatIso.ofComponents (fun M ↦
    { hom := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      inv := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      hom_inv_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp })
    (by
      intro M N f
      apply SheafOfModules.strictRingSystem_hom_ext
      intro n
      change f.app n ≫ 𝟙 _ = 𝟙 _ ≫ f.app n
      simp)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun n ↦ Iso.refl _)
    (by
      intro n m h
      change F.map _ ≫ 𝟙 _ = 𝟙 _ ≫ F.map h
      simp only [Category.comp_id, Category.id_comp])) (by intro M N f; ext n; exact rfl)
  functor_unitIso_comp M := by ext n; simp [independentToTower]

/-- The real constant-ring sequence equivalence, including its specified inverse.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentConstantSequenceEquivalence :
    systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O) ≌
      (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) :=
  (strictSystemSequenceEquivalence.{c, v, max c v r}
    ((Functor.const ℕᵒᵖ).obj O)).symm.trans (independentSystemTowerEquivalence.{c, v, r} O)

/-- Both explicit functors preserve sums.
Source: Stacks 03DA, 0940 (blueprint: def-coef-constant-sequence-equivalence).
Proof: the strict-system realization adds section maps componentwise; so do the
explicit forward and inverse tower functors. Their composites therefore add maps. -/
theorem independentConstantSequenceEquivalence_additive :
    (independentConstantSequenceEquivalence.{c, v, r} O).functor.Additive ∧
      (independentConstantSequenceEquivalence.{c, v, r} O).inverse.Additive := by
  have h : (independentConstantSequenceEquivalence.{c, v, r} O).functor.Additive := by
    constructor
    intro M N f g
    apply NatTrans.ext
    funext n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl
  exact ⟨h, (independentConstantSequenceEquivalence.{c, v, r} O).inverse_additive⟩

end CategoryTheory.ConstantCompletion
