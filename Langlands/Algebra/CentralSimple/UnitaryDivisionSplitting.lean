import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.Algebra.CentralSimple.MatrixSemilinearInvolution
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Unitary involutions on central simple algebras: from division algebras to splitting -/

universe u

namespace Langlands.Algebra.CentralSimple

open Matrix

/-- If a matrix algebra `Matrix ι ι D` with nonempty index type is central over `L`, then
so is `D`. -/
theorem isCentral_of_matrix {L D ι : Type*} [CommSemiring L] [Semiring D] [Algebra L D]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Algebra.IsCentral L (Matrix ι ι D)] :
    Algebra.IsCentral L D where
  out d hd := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hd' : ∀ r, Commute d r := fun r => (Subalgebra.mem_center_iff.1 hd r).symm
    have hmem : scalar ι d ∈ Subalgebra.center L (Matrix ι ι D) :=
      Subalgebra.mem_center_iff.2 fun M => (scalar_commute d hd' M).symm
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff L).1 hmem
    refine Algebra.mem_bot.2 ⟨c, ?_⟩
    have := congrFun (congrFun hc i) i
    simpa [algebraMap_matrix_apply] using this.symm

/-- A finite-dimensional algebra of dimension one over a field `L` is `L` itself. -/
noncomputable def algEquivOfFinrankEqOne {L D : Type*} [Field L] [DivisionRing D] [Algebra L D]
    (h : Module.finrank L D = 1) : L ≃ₐ[L] D :=
  AlgEquiv.ofBijective (Algebra.ofId L D)
    ⟨(algebraMap L D).injective, fun d => by
      have hd : d ∈ (⊤ : Subalgebra L D) := Algebra.mem_top
      rw [← Subalgebra.bot_eq_top_of_finrank_eq_one h, Algebra.mem_bot] at hd
      exact hd⟩

/-- **Division-to-splitting implication for unitary involutions.** Over every field `K`,
if central division algebras with a unitary involution over separable quadratic extensions
of `K` are commutative, then central simple algebras with a unitary involution over such
extensions are split. -/
theorem unitaryDivisionSplitting : UnitaryDivisionSplittingStatement.{u} := by
  intro K _ hDiv L _ _ _ _ σ hσ B _ _ _ _ _ τ hτ
  have : IsArtinianRing B := IsArtinianRing.of_finite L B
  obtain ⟨n, hn, D, _, _, _, ⟨Φ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L B
  have : Algebra.IsCentral L (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv L B _ Φ
  have : Algebra.IsCentral L D := isCentral_of_matrix (ι := Fin n)
  have hσ' : ∃ ω, (σ : L →+* L) ω ≠ ω := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  obtain ⟨θ, θ_add, θ_mul, θ_invol, θ_alg⟩ :=
    exists_semilinear_involution_of_algEquiv_matrix Φ (σ : L →+* L) hσ' τ hτ.1 hτ.2.1 hτ.2.2.1
      hτ.2.2.2
  have hD : Module.finrank L D = 1 := hDiv L σ hσ D θ ⟨θ_add, θ_mul, θ_invol, θ_alg⟩
  exact ⟨n, ⟨Φ.trans (AlgEquiv.mapMatrix (algEquivOfFinrankEqOne hD).symm)⟩⟩

end Langlands.Algebra.CentralSimple
