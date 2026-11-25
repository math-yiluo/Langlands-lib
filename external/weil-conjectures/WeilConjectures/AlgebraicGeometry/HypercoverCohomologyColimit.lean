/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type w) [Category.{v} A] [Abelian A]

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
noncomputable def cohomologyFunctor (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).obj U.simplicial.rightOp ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
noncomputable def cohomologyRefinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) (q : ℕ) : cohomologyFunctor A V q ⟶ cohomologyFunctor A U q :=
  whiskerRight
    (whiskerLeft (sheafToPresheaf X.smallEtaleTopology A)
      ((whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).map f.rightOp))
    (AlgebraicTopology.alternatingCofaceMapComplex A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q)

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def IsCohomologyColimit (q : ℕ) (H : Sheaf X.smallEtaleTopology A ⥤ A) : Prop :=
  (∀ (U V : FiniteSplitEtaleHypercover X) (f g : U.Refinement V),
    isRefinementHomotopic f g → cohomologyRefinement A f q = cohomologyRefinement A g q) ∧
  ∃ c : ∀ U : FiniteSplitEtaleHypercover X, cohomologyFunctor A U q ⟶ H,
    (∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V),
      cohomologyRefinement A f q ≫ c U = c V) ∧
    ∀ (F : Sheaf X.smallEtaleTopology A) (B : A)
      (d : ∀ U : FiniteSplitEtaleHypercover X, (cohomologyFunctor A U q).obj F ⟶ B),
      (∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V),
        (cohomologyRefinement A f q).app F ≫ d U = d V) →
      ∃! e : H.obj F ⟶ B, ∀ U : FiniteSplitEtaleHypercover X, (c U).app F ≫ e = d U

end AlgebraicGeometry.FiniteSplitEtaleHypercover
