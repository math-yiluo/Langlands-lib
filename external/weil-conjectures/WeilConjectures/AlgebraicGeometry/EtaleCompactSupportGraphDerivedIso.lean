/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# Invertibility of the graph comparison on unbounded complexes

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 0F0C
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The specified graph map is invertible after unbounded derived descent for a
quasi-compact separated etale morphism over an arbitrary scheme.
Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6 and 0F0C.
(auxiliary; not a blueprint node).

Proof:
1. Mathlib's IsFinite.of_locallyQuasiFinite shows that the quasi-compact etale
geometric fibre is finite over the Artinian spectrum of an algebraically closed field.
Apply the proved finite-etale graph isomorphism theorem to its pulled-back compactification.
2. The geometric base-change graph equation identifies the pulled-back comparison,
after the compact-support exchange, with the invertible sum exchange followed by the
finite-fibre comparison. Torsion proper base change makes the compact-support exchange
invertible. Cancellation makes the pulled-back comparison invertible.
3. The canonical exact/left-derived inverse-image isomorphism identifies these maps
with the left-derived geometric pullbacks. The established geometric-point detection
theorem proves invertibility of every component on arbitrary unbounded complexes.
Componentwise invertibility proves invertibility of the natural transformation.
Only the graph base-change identity remains a separate geometric obligation here. -/
theorem isIso_compactSupportGraphDerivedComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    (c : Compactification f) :
    IsIso (compactSupportDerivedComparison A f c
      (etaleCompactificationGraphMap A f c)) := by
  have happ : ∀ K, IsIso ((compactSupportDerivedComparison A f c
      (etaleCompactificationGraphMap A f c)).app K) := by
    intro K
    apply isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective A
      (fun y : X ↦ X.algClosurePoint y)
      (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩)
    intro y
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (X.algClosurePoint y)) _).2
    have : IsFinite (pullback.fst (X.algClosurePoint y) f) :=
      IsFinite.of_locallyQuasiFinite _
    have := isIso_compactSupportGraphDerivedComparison_of_isFinite A
      (pullback.fst (X.algClosurePoint y) f)
      (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
      isAddTorsion_of_finite (IsPullback.of_hasPullback c.g (X.algClosurePoint y))
    have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip c
    have : IsIso (exactCompactSupportExchange A c (X.algClosurePoint y)) := by
      unfold exactCompactSupportExchange
      infer_instance
    have heq := NatTrans.congr_app
      (compactSupportGraphDerivedComparison_geometric_baseChange A f c y) K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at heq
    have hc : IsIso
        ((upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory.map
          ((compactSupportDerivedComparison A f c
            (etaleCompactificationGraphMap A f c)).app K) ≫
          (exactCompactSupportExchange A c (X.algClosurePoint y)).app K) := by
      rw [heq]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hc
  exact NatIso.isIso_of_isIso_app _

/-- The inverse of the explicitly constructed derived graph map.
Source: SGA 4 XVII 6.2.11
(auxiliary; not a blueprint node). -/
noncomputable def canonicalEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory :=
  haveI := isIso_compactSupportGraphDerivedComparison A f c
  (asIso (compactSupportDerivedComparison A f c
    (etaleCompactificationGraphMap A f c))).symm

end AlgebraicGeometry.Etale
