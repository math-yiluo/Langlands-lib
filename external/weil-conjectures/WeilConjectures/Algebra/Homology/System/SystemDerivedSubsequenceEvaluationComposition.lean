/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence

/-! # The actual derived transitions of strict systems

Source: Zheng, Construction 4.1; Stacks 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The exact subsequence compositor commutes with the selected evaluation
comparisons. Source: Stacks 015F
(blueprint: lem-pur-system-derived-subsequence-evaluation-composition).
Proof: localize and cancel the final evaluation factorization. On complexes the
restriction compositor factorization and the two evaluation factorization equations
reduce both sides to the same three successive factorization maps. Naturality of the
second evaluation comparison moves the first restriction factorization past it. -/
theorem systemDerivedSubsequenceEvaluation_composition (r s : ℕ ↪o ℕ) (c : ℕ)
    (M : DerivedCategory (StrictRingSystem B)) :
    (derivedSystemEvaluation (selectedSystemRings B (s.trans r)) c).map
        ((systemDerivedSubsequenceComposition B r s).hom.app M) ≫
      (systemDerivedSubsequenceEvaluation B (s.trans r) c).hom.app M =
    (systemDerivedSubsequenceEvaluation (selectedSystemRings B r) s c).hom.app
        ((derivedSystemSubsequence B r).obj M) ≫
      (systemDerivedSubsequenceEvaluation B r (s c)).hom.app M := by
  let Ur := systemSubsequence B r
  let Us := systemSubsequence (selectedSystemRings B r) s
  let V := systemEvaluation (selectedSystemRings B (s.trans r)) c
  let W := systemEvaluation B (r (s c))
  let α := (systemDerivedSubsequenceEvaluation (selectedSystemRings B r) s c).hom
  let δ := systemDerivedSubsequenceComposition B r s
  let σ₁ := Functor.whiskerRight δ.hom V.mapDerivedCategory ≫
    (systemDerivedSubsequenceEvaluation B (s.trans r) c).hom
  let σ₂ := Functor.whiskerLeft Ur.mapDerivedCategory α ≫
    (systemDerivedSubsequenceEvaluation B r (s c)).hom
  have he : σ₁ = σ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
    intro K
    let Kr := (Ur.mapHomologicalComplex (.up ℤ)).obj K
    apply (cancel_mono (W.mapDerivedCategoryFactors.hom.app K)).1
    dsimp only [σ₁, σ₂, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    erw [systemDerivedSubsequenceEvaluation_rep B (s.trans r) c K,
      systemDerivedSubsequenceEvaluation_rep B r (s c) K]
    erw [← V.mapDerivedCategory.map_comp_assoc,
      systemDerivedSubsequenceComposition_rep B r s K]
    simp only [Functor.map_comp, Category.assoc]
    have hn := α.naturality (Ur.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [systemDerivedSubsequenceEvaluation_rep (selectedSystemRings B r) s c Kr]
    rfl
  exact congrArg (fun α ↦ α.app M) he

end SheafOfModules
