/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts

/-! # A torsion bound and finite residue generators for an integral local system -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A sufficiently high scalar power has locally free image. Its quotient has a
locally finite free module of canonical generators.

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), and the
continuous Smith invariant argument in the parent integral resolution node.

Proof: choose the power and finite quotient charts from
integral_lfp_finite_quotient_charts. Apply the proved free-generator comparison:
free module objects commute with pullback and send a finite constant sheaf of sets
to the finite biproduct of regular modules indexed by that set. The image statement
is unchanged. The construction also covers a zero quotient, whose underlying set
has one element, and empty schemes. -/
theorem integral_lfp_eventual_free_image
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ N : ℕ,
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj
            (image ((ℓ ^ N) • 𝟙 P)))) ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj
            (moduleObjectFreeGenerators _ (cokernel ((ℓ ^ N) • 𝟙 P))))) := by
  obtain ⟨N, hI, hQ⟩ := integral_lfp_finite_quotient_charts X ℓ E P hP
  exact ⟨N, hI, moduleObjectFreeGenerators_locallyFree X _ _ hQ⟩

end AlgebraicGeometry.ProEtale
