import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Separation of finite coefficient spaces by ideal powers -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.AdicCoefficientSeparation

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

/-- The actual ideal-power quotient map restricted to a coefficient subspace. -/
def quotientOn (I : Ideal A) (N : ℕ) (W : Submodule k A) :
    W →ₗ[k] (A ⧸ I ^ N) :=
  ((Ideal.Quotient.mkₐ k (I ^ N)).toLinearMap).comp W.subtype

/-- A separated decreasing sequence of subspaces eventually misses any fixed
finite-dimensional subspace. -/
theorem exists_comap_eq_bot
    (F : ℕ → Submodule k A) (hF : Antitone F) (hsep : ⨅ N, F N = ⊥)
    (W : Submodule k A) [FiniteDimensional k W] :
    ∃ N, (F N).comap W.subtype = ⊥ := by
  let f : ℕ →o (Submodule k W)ᵒᵈ :=
    ⟨fun N => (F N).comap W.subtype, fun _ _ h => Submodule.comap_mono (hF h)⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨N, eq_bot_iff.mpr ?_⟩
  intro x hx
  have hall : (x : A) ∈ ⨅ i, F i := by
    rw [Submodule.mem_iInf]
    intro i
    have hlarge : x ∈ (F (max N i)).comap W.subtype := by
      have heq : (F N).comap W.subtype = (F (max N i)).comap W.subtype :=
        hN _ (le_max_left _ _)
      exact heq ▸ hx
    exact hF (le_max_right N i) hlarge
  rw [hsep, Submodule.mem_bot] at hall
  change x = 0
  exact Subtype.ext hall

/-- One ideal-power quotient is injective on any supplied finite-dimensional
subspace of a Noetherian domain. -/
theorem exists_quotient_injective [IsNoetherianRing A] [IsDomain A]
    (I : Ideal A) (hI : I ≠ ⊤)
    (W : Submodule k A) [FiniteDimensional k W] :
    ∃ N, Function.Injective (quotientOn I N W) := by
  obtain ⟨N, hN⟩ := exists_comap_eq_bot
    (fun N => (I ^ N).restrictScalars k)
    (fun _ _ h x hx => Ideal.pow_le_pow_right h hx) (by
      rw [← Submodule.restrictScalars_iInf, I.iInf_pow_eq_bot_of_isDomain hI]
      rfl) W
  refine ⟨N, LinearMap.ker_eq_bot.mp ?_⟩
  convert hN using 1
  ext x
  change Ideal.Quotient.mk (I ^ N) (x : A) = 0 ↔ (x : A) ∈ I ^ N
  exact Ideal.Quotient.eq_zero_iff_mem

/-- At one bound, every linear functional on the original algebra can be
reproduced on the whole coefficient space by a functional on the quotient. -/
theorem exists_quotient_functionals [IsNoetherianRing A] [IsDomain A]
    (I : Ideal A) (hI : I ≠ ⊤)
    (W : Submodule k A) [FiniteDimensional k W] :
    ∃ N, ∀ ℓ : A →ₗ[k] k, ∃ q : (A ⧸ I ^ N) →ₗ[k] k,
      ∀ x ∈ W, q (Ideal.Quotient.mk (I ^ N) x) = ℓ x := by
  obtain ⟨N, hN⟩ := exists_quotient_injective I hI W
  let f := quotientOn I N W
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hN)
  refine ⟨N, fun ℓ => ⟨(ℓ.comp W.subtype).comp g, ?_⟩⟩
  intro x hx
  have h := LinearMap.congr_fun hg (⟨x, hx⟩ : W)
  change g (Ideal.Quotient.mk (I ^ N) x) = ⟨x, hx⟩ at h
  change ℓ ((g (Ideal.Quotient.mk (I ^ N) x) : W) : A) = ℓ x
  rw [h]

end Langlands.LinearAlgebra.AdicCoefficientSeparation
