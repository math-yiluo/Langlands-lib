import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! # Finite algebras over semi-local rings -/

universe u v

namespace Langlands.Algebra

/-- Every module-finite algebra over `R` has trivial Picard group. -/
def FiniteAlgebrasHaveTrivialPicard (R : Type u) [CommRing R] : Prop :=
  ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A],
    Subsingleton (CommRing.Pic A)

/-- A module-finite algebra over a semi-local ring is semi-local. -/
theorem finiteMaximalSpectrum_of_moduleFinite
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Finite (MaximalSpectrum R)] [Module.Finite R A] :
    Finite (MaximalSpectrum A) := by
  let s : Set (PrimeSpectrum R) := Set.range MaximalSpectrum.toPrimeSpectrum
  have hs : s.Finite := Set.finite_range _
  have ht := Algebra.QuasiFinite.finite_comap_preimage (S := A) hs
  let : Finite (PrimeSpectrum.comap (algebraMap R A) ⁻¹' s) := ht.to_subtype
  let f : MaximalSpectrum A → (PrimeSpectrum.comap (algebraMap R A) ⁻¹' s) :=
    fun m => ⟨m.toPrimeSpectrum, by
      refine ⟨⟨m.asIdeal.under R, inferInstance⟩, ?_⟩
      rfl⟩
  exact Finite.of_injective f fun m n h =>
    MaximalSpectrum.toPrimeSpectrum_injective (congrArg Subtype.val h)

/-- Every finite algebra over a semi-local ring has trivial Picard group. -/
theorem finiteAlgebrasHaveTrivialPicard_of_semilocal
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)] :
    FiniteAlgebrasHaveTrivialPicard.{u, v} R := by
  intro A _ _ _
  let := finiteMaximalSpectrum_of_moduleFinite R A
  infer_instance

end Langlands.Algebra
