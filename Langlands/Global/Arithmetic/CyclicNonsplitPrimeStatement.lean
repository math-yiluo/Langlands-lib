import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Nonsplit finite primes in nontrivial cyclic extensions -/

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension

universe u v

/-- A nontrivial cyclic extension of number fields has a finite prime with
nontrivial completed degree outside every finite set. This states the cyclic
number-field specialization of Artin–Tate V §4, Theorem 2. -/
def CyclicNonsplitPrimeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    1 < Module.finrank F E →
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧
        ∃ (w : HeightOneSpectrum (𝓞 E)) (h : w.asIdeal.LiesOver v.asIdeal),
          letI := h
          Module.finrank (v.adicCompletion F) (w.adicCompletion E) ≠ 1

end Langlands.Global
