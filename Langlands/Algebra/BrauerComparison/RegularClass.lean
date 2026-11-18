import Langlands.Algebra.BrauerComparison.Relative
import Langlands.Algebra.BrauerComparison.RegularDescent

/-! # Realization of every finite-relative degree-two class -/

noncomputable section

open scoped TensorProduct

universe u

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local (relativeCohomology)
open ScalarTwoCocycle (IsTwoCocycle)

attribute [local instance] Classical.decEq

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The regular descended chart recovers the class of the very cocycle used to construct it. -/
theorem relativeClass_regularSplittingChart
    (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    relativeClass (regularSplittingChart c hc) = unitClass c hc := by
  unfold relativeClass
  exact descentClass_eq_of_lifts _ (regularLift c) c
    (fun s X => (regularSplittingChart_action c hc s X).trans (regularAction_apply c hc s X))
    (regularLift_mul c hc)

/-- Realize a relative cohomology class by an actual central simple algebra and splitting chart. -/
def regularClassRepresentative (x : relativeCohomology K L 2) :
    Σ A : CSA.{u, u} K, {e : L ⊗[K] A ≃ₐ[L] Matrix (Gal(L/K)) (Gal(L/K)) L //
      relativeClass e = x} := by
  let c := (exists_unitClass_eq x).choose
  have hc : IsTwoCocycle c := (exists_unitClass_eq x).choose_spec.choose
  exact ⟨regularCSA c hc, regularSplittingChart c hc,
    (relativeClass_regularSplittingChart c hc).trans (exists_unitClass_eq x).choose_spec.choose_spec⟩

/-- Every ordinary relative class has an actual finite Galois splitting chart realizing it. -/
theorem exists_relativeClass_eq (x : relativeCohomology K L 2) :
    ∃ (A : CSA.{u, u} K) (e : L ⊗[K] A ≃ₐ[L] Matrix (Gal(L/K)) (Gal(L/K)) L),
      relativeClass e = x :=
  ⟨(regularClassRepresentative x).1, (regularClassRepresentative x).2.1,
    (regularClassRepresentative x).2.2⟩

end Langlands.BrauerComparison
