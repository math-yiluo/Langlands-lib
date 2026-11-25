/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison

/-! Expansion of the canonical second pullback comparison. -/

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

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The second pullback comparison is the composite of the two twist comparisons and
transport of the ambient square comparison. This exposes the factorization used in the
section restriction calculation. -/
theorem second_pull_comparison_inv_expansion
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (secondPullComparison l c k p hpl Y K).inv =
      (pullTwistIso (coefficient l c).X (firstProjection Y) _ _
        (shiftedLineComparison l c (firstProjection Y))
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) ≪≫
      (twist (coefficient l c).X (diagonalSurface Y)
        (line l c (diagonalSurface Y))).mapIso
        ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K) ≪≫
      (pullTwistIso (coefficient l c).X (secondProjection Y) _ _
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)).symm).inv := by
  have hp : hproj = (fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible) :=
    Subsingleton.elim _ _
  have hd : hdiag = (fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible) :=
    Subsingleton.elim _ _
  subst hproj hdiag
  unfold secondPullComparison
  rfl

/-- The inverse expansion after applying diagonal pullback. This is the form used by
section restriction, so rewriting does not unfold the large comparison definition. -/
theorem second_pull_comparison_inv_map_expansion
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        (secondPullComparison l c k p hpl Y K).inv =
      (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        (pullTwistIso (coefficient l c).X (firstProjection Y) _ _
          (shiftedLineComparison l c (firstProjection Y))
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) ≪≫
        (twist (coefficient l c).X (diagonalSurface Y)
          (line l c (diagonalSurface Y))).mapIso
          ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K) ≪≫
        (pullTwistIso (coefficient l c).X (secondProjection Y) _ _
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)).symm).inv := by
  rw [second_pull_comparison_inv_expansion l c k p hpl Y K]

end AlgebraicGeometry.ProEtale.RationalP1
