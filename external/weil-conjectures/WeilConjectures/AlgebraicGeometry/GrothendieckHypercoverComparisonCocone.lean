/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverCohomology
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverResolution
import WeilConjectures.AlgebraicGeometry.GrothendieckInjectiveHypercoverRow

/-! # The explicit comparison cocone for hypercover cohomology -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- The comparison constructed from the two augmentations of the section bicomplex. -/
noncomputable def canonicalComparison (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    cohomologyFunctor A U q ⟶ (terminalSections A).rightDerived q :=
  comparisonNat A (fun U F h ↦ by
    have := h
    exact injective_row_quasiIso A U F) U q

lemma canonicalComparison_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) (q : ℕ) :
    cohomologyRefinement A f q ≫ canonicalComparison A U q = canonicalComparison A V q :=
  comparisonNat_refinement A _ f q

set_option backward.isDefEq.respectTransparency false in
/-- The comparison cocone on the actual filtered homotopy quotient of hypercovers. -/
noncomputable def comparisonCocone (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    Cocone (homotopyCohomologyDiagram A F q) where
  pt := ((terminalSections A).rightDerived q).obj F
  ι :=
    { app := fun U ↦ (canonicalComparison A U.as.unop q).app F
      naturality := by
        rintro ⟨U⟩ ⟨V⟩ f
        refine Quot.inductionOn f ?_
        intro f
        change (cohomologyRefinement A f.unop.hom q).app F ≫
          (canonicalComparison A V.unop q).app F =
          (canonicalComparison A U.unop q).app F ≫ 𝟙 _
        simpa only [Category.comp_id, NatTrans.comp_app] using
          congrArg (fun t ↦ t.app F) (canonicalComparison_refinement A f.unop.hom q) }

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
