import Langlands.Representation.Jacquet.CompactUnionCoinvariantStatements
import Langlands.HarmonicAnalysis.Distribution.RenardHaarLeftProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The left-regular test-function coinvariants form a line -/

noncomputable section

namespace Langlands.Jacquet

open HarmonicAnalysis HarmonicAnalysis.Distribution

universe uH

/-- Renard III.2.9, Example: Haar integration identifies the left-regular
coinvariants of the test functions with a one-dimensional complex vector space. -/
theorem haarCoinvariantsDimension : HaarCoinvariantsDimensionStatement.{uH} := by
  intro G _ _ _ _ _ _
  let ρ := GroupAction.leftTests (G := G)
  obtain ⟨T, -, hTl, huniq⟩ := RenardHaar.leftHaar G
  have hT : T ≠ 0 := by
    intro hzero
    obtain ⟨c, -, hc⟩ := huniq T hTl
    have h0 : (0 : ℂ) = c := hc 0 (by simp [hzero])
    have h1 : (1 : ℂ) = c := hc 1 (by simp)
    exact zero_ne_one (h0.trans h1.symm)
  have hinv : ∀ g : (⊤ : Subgroup G), T ∘ₗ ρ g = T := by
    intro g
    ext f
    change T (GroupAction.leftTests (g : G) f) = T f
    have h := congrArg (fun D : Distribution G => D f) (hTl (g : G)⁻¹)
    simpa only [GroupAction.leftDistributions_apply, inv_inv] using h
  let I : Coinvariants ρ ⊤ →ₗ[ℂ] ℂ := lift ρ ⊤ T hinv
  have hker : ∀ q, I q = 0 → q = 0 := by
    intro q hq
    apply (Module.forall_dual_apply_eq_zero_iff ℂ q).mp
    intro φ
    let S : Distribution G := φ.comp (mk ρ ⊤)
    have hSl : IsLeftInvariant S := by
      intro g
      ext f
      change φ (mk ρ ⊤ (ρ g⁻¹ f)) = φ (mk ρ ⊤ f)
      exact congrArg φ (mk_apply_subgroup ρ ⊤ ⟨g⁻¹, Subgroup.mem_top _⟩ f)
    obtain ⟨c, hc, -⟩ := huniq S hSl
    obtain ⟨f, rfl⟩ := mk_surjective ρ ⊤ q
    have hf := congrArg (fun D : Distribution G => D f) hc
    change φ (mk ρ ⊤ f) = c * T f at hf
    change T f = 0 at hq
    simpa only [hq, mul_zero] using hf
  have hIinj : Function.Injective I := by
    intro q r h
    apply sub_eq_zero.mp
    apply hker (q - r)
    rw [map_sub, h, sub_self]
  have hI : I ≠ 0 := by
    intro hzero
    apply hT
    ext f
    have hf := congrArg (fun F : Coinvariants ρ ⊤ →ₗ[ℂ] ℂ => F (mk ρ ⊤ f)) hzero
    exact hf
  have hIsurj : Function.Surjective I :=
    surjective_of_nonzero_of_finrank_eq_one (Module.finrank_self ℂ) hI
  exact (LinearEquiv.ofBijective I ⟨hIinj, hIsurj⟩).finrank_eq.trans
    (Module.finrank_self ℂ)

end Langlands.Jacquet
