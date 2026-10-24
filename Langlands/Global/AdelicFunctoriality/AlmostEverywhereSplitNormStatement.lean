import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Idele-class norms when almost every finite completion has degree one -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension

universe u v

/-- The approximation step in Artin–Tate V §4, Theorem 2: if a cyclic
number-field extension has completed degree one outside a finite set of finite
primes, its actual idele-class norm is surjective. This defines a proposition. -/
def AlmostEverywhereSplitIdeleClassNormSurjective : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ (p : HeightOneSpectrum (𝓞 F)), p ∉ S →
        ∀ (q : HeightOneSpectrum (𝓞 E)) (h : q.asIdeal.LiesOver p.asIdeal),
          letI := h
          Module.finrank (p.adicCompletion F) (q.adicCompletion E) = 1) →
      Function.Surjective (ideleClassNorm (K := F) (L := E))

end Langlands.Global.AdelicFunctoriality
