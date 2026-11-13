import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Essentially smooth algebras and truncated local rings

Notions used in Section 11 ("Inseparable residue fields") of the Stacks Project chapter
"Smoothing ring maps" (smoothing.pdf). -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- `S` is essentially smooth over `R`: `S` is a localization of a smooth `R`-algebra (the
smooth analogue of Stacks Algebra Definition 10.54.1, "essentially of finite type"). -/
def EssentiallySmooth (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S) (_ : IsScalarTower R T S)
    (M : Submonoid T), Algebra.Smooth R T ∧ IsLocalization M S

/-- The truncation `Λ_q / qⁿΛ_q` of the local ring of `Λ` at a prime `q`. -/
abbrev localTruncation {Λ : Type u} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] (n : ℕ) : Type u :=
  Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n

/-- The canonical ring map `Λ → Λ_q / qⁿΛ_q`. -/
def toLocalTruncation {Λ : Type u} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] (n : ℕ) :
    Λ →+* localTruncation q n :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n)).comp
    (algebraMap Λ (Localization.AtPrime q))

end Langlands.CommutativeAlgebra.Popescu
