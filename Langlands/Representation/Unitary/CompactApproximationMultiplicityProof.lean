import Langlands.Representation.Unitary.CompactApproximationMultiplicityStatement
import Langlands.Analysis.CompactApproximationEigenspaceProof
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

namespace Langlands.Analysis

universe uG uE

/-- Compatible compact approximations bound the number of equivalent members
of an actual orthogonal family. -/
theorem compactApproximationMultiplicity :
    CompactApproximationMultiplicityStatement.{uG, uE} := by
  classical
  intro G _ E _ _ _ π _ T hcompact hsymm hlim hpres hcompat A hA horth P hP
  obtain ⟨n, μ, hμ0, hPF, _⟩ :=
    compactApproximationEigenspace E T hcompact hsymm hlim P (hA P hP).1
      (hA P hP).2.1 (fun n => hpres n P (hA P hP).2.1 (hA P hP).2.2)
  let F : Submodule ℂ E := Module.End.eigenspace (T n).toLinearMap μ
  have : FiniteDimensional ℂ F :=
    ContinuousLinearMap.finite_dimensional_eigenspace (hcompact n) μ hμ0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPF
  let xp : P := ⟨x, hx.1⟩
  let B : Set (Submodule ℂ E) := {Q | Q ∈ A ∧
    ∃ (U : P ≃ₗᵢ[ℂ] Q), ∀ (g : G) (z : P),
      (U ⟨π g z, (hA P hP).2.2 g z z.2⟩ : E) = π g (U z)}
  let U (Q : B) : P ≃ₗᵢ[ℂ] (Q : Submodule ℂ E) :=
    Classical.choose Q.property.2
  let y (Q : B) : E := U Q xp
  have hxe :
      (⟨T n xp, hpres n P (hA P hP).2.1 (hA P hP).2.2 xp xp.2⟩ : P) =
        μ • xp := by
    apply Subtype.ext
    exact Module.End.mem_eigenspace_iff.mp hx.2
  have hyF (Q : B) : y Q ∈ F := by
    apply Module.End.mem_eigenspace_iff.mpr
    change T n (U Q xp) = μ • (U Q xp : E)
    calc
      T n (U Q xp) =
          (U Q ⟨T n xp, hpres n P (hA P hP).2.1 (hA P hP).2.2 xp xp.2⟩ : E) :=
        (hcompat P Q (hA P hP).2.1 (hA P hP).2.2 (U Q)
          (Classical.choose_spec Q.property.2) n xp).symm
      _ = (U Q (μ • xp) : E) := by rw [hxe]
      _ = μ • (U Q xp : E) := by simp only [map_smul, Submodule.coe_smul]
  have hy0 (Q : B) : y Q ≠ 0 := by
    intro hz
    have hz' : U Q xp = 0 := Subtype.ext hz
    have hxp : xp = 0 :=
      (U Q).injective (hz'.trans (map_zero (U Q)).symm)
    exact hx0 (congrArg (fun z : P => (z : E)) hxp)
  let v (Q : B) : F := ⟨y Q, hyF Q⟩
  have hv : LinearIndependent ℂ v := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro Q h
      exact hy0 Q (congrArg (fun z : F => (z : E)) h)
    · intro Q R hne
      change inner ℂ (y Q) (y R) = 0
      have hQR : (Q : Submodule ℂ E) ≠ (R : Submodule ℂ E) :=
        fun h => hne (Subtype.ext h)
      exact (horth Q.property.1 R.property.1 hQR).inner_eq
        (U Q xp).property (U R xp).property
  have : Finite B := hv.finite
  exact Set.toFinite B

end Langlands.Analysis
