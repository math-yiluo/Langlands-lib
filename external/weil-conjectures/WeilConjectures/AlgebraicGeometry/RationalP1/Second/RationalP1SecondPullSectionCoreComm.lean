/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionCompatibility
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionCoreConjugate

/-! The morphism equation underlying the untwisted diagonal restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection
attribute [local irreducible] square

/-- On the diagonal, the pulled-back ambient comparison followed by the first-projection
pull-section isomorphism equals the second-projection pull-section isomorphism. -/
theorem second_pull_section_core_comm
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) := by
  rw [second_pull_section_core_conjugate l c k p hpl Y K]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale.RationalP1
