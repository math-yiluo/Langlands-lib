/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionCompatibility
import WeilConjectures.AlgebraicGeometry.RationalP1.PullSectionTransport
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionTransportData
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparisonExpansion
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionCoreComm

/-! # The second pullback comparison restricted to the diagonal
-/

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
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] projectionMap singleUnitIso secondLineComparison

/-- The ambient pullback comparison restricts to the identity on the diagonal for the
untwisted base object. -/
theorem second_pull_section_core
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    PullSectionCompatibility
      (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)
      ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv := by
  exact ⟨second_pull_section_core_comm l c k p hpl Y K⟩

-- The statement compares the fixed derived pullback and tensor interfaces.
/-- The two canonical pullback identifications agree after restriction to the diagonal. -/
theorem second_pull_section
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    PullSectionCompatibility
      (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      ((twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (secondPullComparison l c k p hpl Y K).inv := by
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  obtain ⟨data, _⟩ := second_pull_section_transport_data l c k p hpl Y K
  refine ⟨?_⟩
  rw [second_pull_comparison_inv_map_expansion l c k p hpl Y K]
  exact pull_section_transport _ _ _ _ _ _ data
    (second_pull_section_core l c k p hpl Y K).comm

end AlgebraicGeometry.ProEtale.RationalP1
