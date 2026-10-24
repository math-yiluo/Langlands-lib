import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # A degree-prime intermediate-field test for full local degree -/

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension

universe u v

/-- The degree-prime intermediate field detects full local degree in a cyclic
prime-power extension. This is the pointwise reduction underlying
Artin–Tate V §4, Theorem 3; it does not assert the existence of nonsplit primes. -/
def CyclicPrimePowerLocalDegreeReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (ℓ r : ℕ), ℓ.Prime → 0 < r → Module.finrank F E = ℓ ^ r →
    ∃ K : IntermediateField F E,
      IsGalois F K ∧ IsCyclic (K ≃ₐ[F] K) ∧ Module.finrank F K = ℓ ∧
        ∀ (v : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 K))
          (hq : q.asIdeal.LiesOver v.asIdeal),
          letI := hq
          Module.finrank (v.adicCompletion F) (q.adicCompletion K) ≠ 1 →
            ∃ (w : HeightOneSpectrum (𝓞 E)) (_hwq : w.asIdeal.LiesOver q.asIdeal)
              (hwv : w.asIdeal.LiesOver v.asIdeal),
              letI := hwv
              Module.finrank (v.adicCompletion F) (w.adicCompletion E) =
                Module.finrank F E

end Langlands.Global
