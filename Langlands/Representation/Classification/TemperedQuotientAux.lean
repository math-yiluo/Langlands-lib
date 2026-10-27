import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Data.Fin.Rev

/-! # Algebraic adapters for the independent tempered quotient argument -/

noncomputable section

namespace Langlands.Classification

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Pull a smooth functional back along a map out of the smooth dual, then use
inverse bidual evaluation to land in the original representation. -/
def smoothDualPullbackToOriginal
    (hρ : IsSmooth ρ) (hbidual : Function.Bijective (smoothBidual hρ))
    (a : (smoothContragredient ρ).IntertwiningMap σ) :
    (smoothContragredient σ).IntertwiningMap ρ :=
  ((smoothBidual hρ).ofBijective hbidual).symm.toIntertwiningMap.comp
    (contragredientMap a)

/-- Smooth separation in the ambient module and reflexivity of the original
irreducible module make the bidual pullback construction surjective. -/
theorem smoothDualPullbackToOriginal_surjective
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hbidual : Function.Bijective (smoothBidual hρ))
    (hseparate : Function.Injective (smoothBidual hσ))
    [Representation.IsIrreducible ρ]
    (a : (smoothContragredient ρ).IntertwiningMap σ) (ha : a ≠ 0) :
    Function.Surjective (smoothDualPullbackToOriginal hρ hbidual a) := by
  let e := (smoothBidual hρ).ofBijective hbidual
  let q := smoothDualPullbackToOriginal hρ hbidual a
  have hq : q ≠ 0 := by
    intro hz
    apply ha
    ext v
    simp only [Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
    apply hseparate
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    have hdual : contragredientMap a ℓ = 0 := by
      apply e.symm.injective
      change q ℓ = e.symm 0
      simpa using
        congrArg (fun f : (smoothContragredient σ).IntertwiningMap ρ => f ℓ) hz
    rw [map_zero]
    change ℓ.val (a v) = 0
    exact congrArg
      (fun ψ : SmoothDual (smoothContragredient ρ) => ψ.val v) hdual
  exact (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right hq

/-- A nonzero map out of the smooth dual gives an actual quotient of the
original irreducible representation. -/
theorem exists_surjective_from_smoothDual_of_nonzero
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hbidual : Function.Bijective (smoothBidual hρ))
    (hseparate : Function.Injective (smoothBidual hσ))
    [Representation.IsIrreducible ρ]
    (a : (smoothContragredient ρ).IntertwiningMap σ) (ha : a ≠ 0) :
    ∃ q : (smoothContragredient σ).IntertwiningMap ρ,
      Function.Surjective q :=
  ⟨smoothDualPullbackToOriginal hρ hbidual a,
    smoothDualPullbackToOriginal_surjective hρ hσ hbidual hseparate a ha⟩

/-- Only the original irreducible representation needs admissibility. -/
theorem exists_surjective_from_smoothDual_of_admissible
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hσ : IsSmooth σ)
    [Representation.IsIrreducible ρ]
    (a : (smoothContragredient ρ).IntertwiningMap σ) (ha : a ≠ 0) :
    ∃ q : (smoothContragredient σ).IntertwiningMap ρ,
      Function.Surjective q :=
  exists_surjective_from_smoothDual_of_nonzero hρ.1 hσ
    ⟨smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
      smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩
    (smoothBidual_injective_of_compact_cofinal hcofinal σ hσ) a ha

/-- Reversing the blocks and negating their exponents preserves strict decrease. -/
theorem strictAnti_neg_reverse {r : ℕ} {t : Fin r → ℝ} (ht : StrictAnti t) :
    StrictAnti (fun i : Fin r => -t i.rev) := by
  intro i j hij
  exact neg_lt_neg (ht ((Fin.rev_lt_rev).2 hij))

end Langlands.Classification
