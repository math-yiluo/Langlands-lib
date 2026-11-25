/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition

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

/-- The actual coefficient restriction compositor.
Source: Zheng 4.1; Stacks 015F
(blueprint: lem-pur-system-derived-transition-coherence). -/
def systemDerivedRestrictionComposition {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (systemRestriction B h).mapDerivedCategory ⋙
      (systemRestriction B k).mapDerivedCategory ≅
        (systemRestriction B (h.trans k)).mapDerivedCategory :=
  Functor.exactDerivedRestrictionComposition _ _ _
    (systemScalarRestrictionComposition (B.map (homOfLE k).op)
      (B.map (homOfLE h).op) (B.map (homOfLE (h.trans k)).op) (by
        rw [← B.map_comp]
        rfl))

/-- Derived transitions compose with the canonical coefficient restriction comparison.
Source: Zheng 4.1; Stacks 015F
(blueprint: lem-pur-system-derived-transition-coherence).
Proof: localization detects equality of natural transformations. Postcompose on a
cochain complex with the exact evaluation and restriction factorization isomorphisms.
The transition and compositor representative formulas reduce the two composites to
the localization of the strict composition law, checked termwise on sections. -/
theorem systemDerivedTransition_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (M : DerivedCategory (StrictRingSystem B)) :
    (systemDerivedTransition B k).app M ≫
      (systemRestriction B k).mapDerivedCategory.map ((systemDerivedTransition B h).app M) ≫
      (systemDerivedRestrictionComposition B h k).hom.app
        ((derivedSystemEvaluation B l).obj M) =
    (systemDerivedTransition B (h.trans k)).app M := by
  let V := systemEvaluation B l
  let W := systemEvaluation B m
  let R := systemRestriction B k
  let S := systemRestriction B h
  let U := systemRestriction B (h.trans k)
  let η := systemScalarRestrictionComposition (B.map (homOfLE k).op)
    (B.map (homOfLE h).op) (B.map (homOfLE (h.trans k)).op) (by
      rw [← B.map_comp]
      rfl)
  let δ := systemDerivedRestrictionComposition B h k
  let σ : derivedSystemEvaluation B n ⟶ derivedSystemEvaluation B l ⋙ U.mapDerivedCategory :=
    systemDerivedTransition B k ≫
      Functor.whiskerRight (systemDerivedTransition B h) R.mapDerivedCategory ≫
      Functor.whiskerLeft V.mapDerivedCategory δ.hom
  have he : σ = systemDerivedTransition B (h.trans k) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
    intro K
    let Kl := (V.mapHomologicalComplex (.up ℤ)).obj K
    have hc : ((strictSystemTransition B k).mapHomologicalComplex (.up ℤ)).app K ≫
        (R.mapHomologicalComplex (.up ℤ)).map
          (((strictSystemTransition B h).mapHomologicalComplex (.up ℤ)).app K) ≫
        (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app Kl =
        ((strictSystemTransition B (h.trans k)).mapHomologicalComplex (.up ℤ)).app K := by
      apply HomologicalComplex.hom_ext
      intro i
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro Z
      ext x
      exact ((K.X i).compose h k Z x).symm
    apply (cancel_mono (U.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app Kl)).1
    dsimp only [σ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.assoc]
    rw [← δ.hom.naturality_assoc]
    erw [Functor.exactDerivedRestrictionComposition_hom_factors S R U η Kl]
    dsimp only [Functor.comp_map]
    erw [← R.mapDerivedCategory.map_comp_assoc, ← R.mapDerivedCategory.map_comp_assoc]
    erw [Category.assoc ((systemDerivedTransition B h).app (DerivedCategory.Q.obj K))
      (S.mapDerivedCategory.map (V.mapDerivedCategoryFactors.hom.app K))
      (S.mapDerivedCategoryFactors.hom.app Kl)]
    erw [systemDerivedTransition_rep B h K]
    simp only [R.mapDerivedCategory.map_comp, Category.assoc]
    have hn := R.mapDerivedCategoryFactors.hom.naturality
      (((strictSystemTransition B h).mapHomologicalComplex (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [reassoc_of% (systemDerivedTransition_rep B k K)]
    erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hc]
    exact (systemDerivedTransition_rep B (h.trans k) K).symm
  exact congrArg (fun α ↦ α.app M) he

end SheafOfModules
