/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LerayEdgeCocycleData
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.AlgebraicGeometry.LerayEdgeGrothendieckComparison
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
/-- Vanishing of positive columns makes the constructed Leray edge invertible.
(blueprint: lem-pc-leray-edge-vanishing-iso)

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.

Proof: the Grothendieck spectral sequence for direct image and global sections
has only its zero column under the stated vanishing hypothesis. Its filtration
therefore collapses, and the canonical edge component is an isomorphism for
every coefficient module and degree. The cocycle hypothesis identifies ε with
this canonical edge: the cycles-to-cohomology map on global sections is surjective,
and the section of the cycle sheaf is uniquely determined by its image under
the cycle inclusion. Thus the displayed cocycle formula determines each edge
component on every cohomology class. -/
theorem leray_edge_isIso_of_vanishing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ε : LerayEdge X Y f) (hε : LerayEdgeCocycle f ε) :
    (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (∀ (q p : ℕ), 0 < p →
        IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F))) →
      ∀ q : ℕ, IsIso ((ε q).app F)) := by
  let := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let : PreservesFiniteLimits G := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  have : PreservesLimits D := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits D := inferInstance
  have hFG : D.IsAcyclicComposablePair G := by
    intro I _ p hp
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    exact (Scheme.Modules.module_pushforward_injective_acyclic f I).2 ⊤ n
  obtain ⟨e, he⟩ := leray_edge_grothendieck_comparison f ε hε hFG
  intro F hvan q
  have hcollapse := (grothendieck_left_edge_cocycle D G hFG F (injectiveResolution F)).2.2
  have hzero : ∀ p q : ℕ, 0 < p →
      IsZero ((G.rightDerived p).obj ((D.rightDerived q).obj F)) := by
    intro p q hp
    exact hvan q p hp
  have : IsIso ((D.grothendieckLeftEdgeMap G hFG q).app F) := hcollapse hzero q
  rw [he q F]
  infer_instance
end AlgebraicGeometry
