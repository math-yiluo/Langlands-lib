import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof

/-! Evaluation on the actual compact mirabolic model detects a functional. -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Translation detects nonzeroness of the evaluation functional whenever
the source carrier is nonzero. -/
theorem mirabolicCompactEvalFunctional_ne_zero [Nontrivial V]
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (e : ξ.Equiv (mirabolicCompactInduced ψ r)) :
    (mirabolicCompactEvalFunctional ψ e).val ≠ 0 := by
  intro hzero
  have hezero : ∀ v : V, e v = 0 := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have hv := LinearMap.congr_fun hzero (ξ g v)
    rw [mirabolicCompactEvalFunctional_apply] at hv
    have he : e (ξ g v) = mirabolicCompactInduced ψ r g (e v) :=
      LinearMap.congr_fun (e.isIntertwining' g) v
    rw [he, mirabolicCompactEval_translate, one_mul] at hv
    exact hv
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply EquivLike.injective e
  simpa only [map_zero] using hezero v

/-- A nonzero carrier equivalent to the actual compact mirabolic model has
a nonzero standard functional. No multiplicity theorem is needed. -/
theorem hasFunctional_of_mirabolicCompactEquiv [Nontrivial V]
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (e : ξ.Equiv (mirabolicCompactInduced ψ r)) :
    HasFunctional (N := Mirabolic.upperUnipotent r F)
      (θ := mirabolicCharacter ψ r) ξ :=
  ⟨mirabolicCompactEvalFunctional ψ e, mirabolicCompactEvalFunctional_ne_zero ψ r ξ e⟩

end Langlands.Whittaker
