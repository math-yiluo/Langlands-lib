/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
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

/-- Selected derived evaluations intertwine the actual derived transition maps.
Source: Zheng 4.1; Stacks 015F
(blueprint: lem-pur-system-derived-subsequence-transition).
Proof: localization detects equality. On each cochain representative, cancel the
exact evaluation and restriction factorization isomorphisms. The selected-evaluation
factorization and transition formulas reduce the result to the same strict transition
at the selected levels. Naturality moves the subsequence factorization through the
transition, and the strict selected transition is definitionally the original one. -/
theorem systemDerivedSubsequenceTransition (r : ℕ ↪o ℕ) {a b : ℕ} (h : a ≤ b)
    (M : DerivedCategory (StrictRingSystem B)) :
    (systemDerivedSubsequenceEvaluation B r b).hom.app M ≫
        (systemDerivedTransition B (r.monotone h)).app M =
      (systemDerivedTransition (selectedSystemRings B r) h).app
          ((derivedSystemSubsequence B r).obj M) ≫
        (systemRestriction B (r.monotone h)).mapDerivedCategory.map
          ((systemDerivedSubsequenceEvaluation B r a).hom.app M) := by
  let R := systemRestriction B (r.monotone h)
  let V := systemEvaluation B (r a)
  let W := systemEvaluation B (r b)
  let U := systemSubsequence B r
  let Va := systemEvaluation (selectedSystemRings B r) a
  let Vb := systemEvaluation (selectedSystemRings B r) b
  let τ := systemDerivedTransition (selectedSystemRings B r) h
  let σ₁ := (systemDerivedSubsequenceEvaluation B r b).hom ≫
    systemDerivedTransition B (r.monotone h)
  let σ₂ := Functor.whiskerLeft U.mapDerivedCategory τ ≫
    Functor.whiskerRight (systemDerivedSubsequenceEvaluation B r a).hom R.mapDerivedCategory
  have he : σ₁ = σ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
    intro K
    let KU := (U.mapHomologicalComplex (.up ℤ)).obj K
    apply (cancel_mono (R.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((V.mapHomologicalComplex (.up ℤ)).obj K))).1
    dsimp only [σ₁, σ₂, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    erw [systemDerivedTransition_rep B (r.monotone h) K,
      reassoc_of% (systemDerivedSubsequenceEvaluation_rep B r b K)]
    simp only [← Functor.map_comp_assoc]
    erw [systemDerivedSubsequenceEvaluation_rep B r a K]
    simp only [Functor.map_comp, Category.assoc]
    erw [← τ.naturality_assoc (U.mapDerivedCategoryFactors.hom.app K)]
    erw [systemDerivedTransition_rep (selectedSystemRings B r) h KU]
    rfl
  exact congrArg (fun α ↦ α.app M) he

end SheafOfModules
