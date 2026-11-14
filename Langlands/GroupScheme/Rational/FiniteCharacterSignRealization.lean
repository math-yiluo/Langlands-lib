import Langlands.LinearAlgebra.RootFaceReflection
import Langlands.Geometry.Building.RealTorusSpace
import Mathlib.Basic.Sign.Basic

/-! # Integral realization of finite actual-character sign patterns -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every finite family of actual characters has the same signs on some
integral cocharacter as on a given real cocharacter vector. -/
theorem exists_cocharacter_sign_eq {ι : Type*} [Fintype ι]
    (α : ι → characterLattice T) (v : V T) :
    ∃ μ : cocharacterLattice T, ∀ i,
      SignType.sign (latticePairing T (α i) μ) = SignType.sign (eval T (α i) v) := by
  classical
  let φ : ι × Bool → cocharacterLattice T →ₗ[ℤ] ℤ :=
    fun j => if j.2 then latticePairing T (α j.1) else -latticePairing T (α j.1)
  let ψ : ι × Bool → V T →ₗ[ℝ] ℝ :=
    fun j => if j.2 then eval T (α j.1) else -eval T (α j.1)
  have hψ : ∀ j (t : ℝ) (n : cocharacterLattice T),
      ψ j (t ⊗ₜ[ℤ] n) = t * (φ j n : ℝ) := by
    rintro ⟨i, b⟩ t n
    cases b <;> simp [φ, ψ, eval_tmul]
  obtain ⟨μ, hμ⟩ :=
    Langlands.LinearAlgebra.RootFaceCone.exists_int_sign_realization
      Finset.univ φ ψ hψ v
  refine ⟨μ, fun i => ?_⟩
  have hpos : 0 < latticePairing T (α i) μ ↔ 0 < eval T (α i) v := by
    simpa [φ, ψ] using hμ (i, true) (Finset.mem_univ _)
  have hneg : latticePairing T (α i) μ < 0 ↔ eval T (α i) v < 0 := by
    simpa [φ, ψ] using hμ (i, false) (Finset.mem_univ _)
  simp only [sign_apply, hpos, hneg]

/-- Set-indexed form of finite integral sign realization. -/
theorem exists_cocharacter_sign_eq_on_finite {s : Set (characterLattice T)}
    (hs : s.Finite) (v : V T) :
    ∃ μ : cocharacterLattice T, ∀ χ ∈ s,
      SignType.sign (latticePairing T χ μ) = SignType.sign (eval T χ v) := by
  let := hs.fintype
  obtain ⟨μ, hμ⟩ := exists_cocharacter_sign_eq (fun χ : s => χ.val) v
  exact ⟨μ, fun χ hχ => hμ ⟨χ, hχ⟩⟩

/-- A chosen genuine integral cocharacter realizing the supplied finite signs. -/
def signRealizingCocharacter (s : Set (characterLattice T)) (hs : s.Finite) (v : V T) :
    cocharacterLattice T :=
  (exists_cocharacter_sign_eq_on_finite hs v).choose

theorem signRealizingCocharacter_spec (s : Set (characterLattice T))
    (hs : s.Finite) (v : V T) (χ : characterLattice T) (hχ : χ ∈ s) :
    SignType.sign (latticePairing T χ (signRealizingCocharacter s hs v)) =
      SignType.sign (eval T χ v) :=
  (exists_cocharacter_sign_eq_on_finite hs v).choose_spec χ hχ

end Langlands.GroupScheme.RealTorusSpace
