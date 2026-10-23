import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Full local degree in cyclic prime-power extensions -/

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension

universe u v

/-- A cyclic extension of prime-power degree has a finite prime of full local degree
outside any prescribed finite set. This states the number-field case of
Artin–Tate V §4, Theorem 3; it does not prove it. -/
def CyclicPrimePowerLocalDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (ℓ r : ℕ), ℓ.Prime → 0 < r → Module.finrank F E = ℓ ^ r →
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧
        ∃ (w : HeightOneSpectrum (𝓞 E)) (h : w.asIdeal.LiesOver v.asIdeal),
          letI := h
          Module.finrank (v.adicCompletion F) (w.adicCompletion E) =
            Module.finrank F E

end Langlands.Global
