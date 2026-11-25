/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSiteOriginComparisonCore

/-! # Bounded-below site comparison on strict coefficient systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

/-- Construct comparison at a fixed etale evaluation package, and restrict its actual
unit and counit to bounded-below objects and finite etale origins.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison).

The core comparison theorem supplies the actual system comparison, its equivalence,
and all levelwise unit, counit, and inverse-origin assertions. Exact evaluation
preserves the common lower bound, while the origin witness in `C.origin` is already
the required finite-level origin witness. -/
theorem exceptionalSiteOriginComparison
    (O : Type (u + 1)) [CommRing O] (ell : O)
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell) :
    ∃ C : ExceptionalSystemSiteComparison O ell T PE,
      ExceptionalSystemSiteEquivalence C ∧
      (∀ n M, C.origin M → C.levelOrigin n ((C.proEvaluation.evaluation n).obj M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) → IsIso ((C.image.level n).adjunction.unit.app M)) ∧
      (∀ n M, C.levelOrigin n M → IsIso ((C.image.level n).adjunction.counit.app M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        C.levelOrigin n ((C.image.level n).inverse.obj M)) := by
  obtain ⟨C, hC, hunit, hcounit, hinv⟩ :=
    exceptionalSiteOriginComparison_core O ell T PE
  refine ⟨C, hC, ?_, hunit, hcounit, hinv⟩
  intro n M hM
  obtain ⟨N, hN, ⟨e⟩⟩ := hM.2 n
  obtain ⟨b, hb⟩ := hN
  have heval : ((C.proEvaluation.evaluation n).obj M).IsGE b := by
    haveI : ((C.image.level n).inverse.obj N).IsGE b :=
      exceptionalSiteOriginComparison_level_inverse_bound O ell T PE C n N b hb
    exact DerivedCategory.TStructure.t.isGE_of_iso e b
  exact ⟨⟨b, heval⟩, N, ⟨b, hb⟩, ⟨e⟩⟩

end AlgebraicGeometry
