/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionComparison
/-! # Koszul reconstruction from strict quotient reductions

## References

* Stacks Tags 091N, 0941, 099M
* Stacks Tags 091N, 091Z, 099L and 099M
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

/-- Koszul completion and the total derived inverse limit of strict quotient reductions
are naturally isomorphic, carrying the Koszul unit to the actual quotient completion unit.
Consequently the quotient unit is invertible for every derived I-complete object. -/
theorem koszulReconstruction (r : ℕ) (a : Fin r → A)
    (_ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ c : reconstructionKoszulDerivedFunctor T d r a ≅
        completedAdicReduction T d ⋙ reconstructionRlim T d,
      (∀ K : DerivedCategory (CompletedAdicModules T d),
        (reconstructionKoszulDerivedUnit T d r a).app K ≫ c.hom.app K =
          (reconstructionCompletionUnit T d).app K) ∧
      (∀ K : DerivedCategory (CompletedAdicModules T d),
        IsIso ((reconstructionKoszulDerivedUnit T d r a).app K) →
          IsIso ((reconstructionCompletionUnit T d).app K)) := by
  obtain ⟨c, hc⟩ := koszulReconstructionComparison T d r a _ha
  refine ⟨c, hc, ?_⟩
  intro K hK
  rw [← hc K]
  infer_instance

end AlgebraicGeometry.Scheme
