import Langlands.CommutativeAlgebra.IntegralFibre.Countable
import Langlands.CommutativeAlgebra.IntegralFibre.SmoothCover
import Langlands.CommutativeAlgebra.LocallySplit.Pi
import Langlands.CommutativeAlgebra.LocallySplit.Projective

/-! # Assembling projectivity from local splitness on smooth localizations

Let `S` be a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every field
`K` over `R`. If `S_s ⊗[R] S` is locally split over `S_s` whenever `S_s` is smooth over `R` with
free differentials, then `S` is projective over `R`. -/

universe u

open TensorProduct

namespace Langlands.CommutativeAlgebra

/-- Let `S` be a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every
field `K` over `R`. If `S_s ⊗[R] S` is locally split over `S_s` for every `s : S` such that `S_s`
is smooth over `R` with free module of differentials, then `S` is a projective `R`-module. -/
theorem projective_of_forall_locallySplit_away {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hS : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] S))
    (H : ∀ s : S, Algebra.Smooth R (Localization.Away s) →
      Module.Free (Localization.Away s) (Ω[Localization.Away s⁄R]) →
      LocallySplit (Localization.Away s) (Localization.Away s ⊗[R] S)) :
    Module.Projective R S := by
  obtain ⟨m, s, h₁, h₂, h₃⟩ := exists_smooth_free_cover hS
  exact projective_of_locallySplit_baseChange (R' := ∀ i, Localization.Away (s i))
    exists_countable_span_eq_top
    (locallySplit_pi (fun i ↦ Localization.Away (s i)) fun i ↦ H (s i) (h₁ i) (h₂ i))

end Langlands.CommutativeAlgebra
