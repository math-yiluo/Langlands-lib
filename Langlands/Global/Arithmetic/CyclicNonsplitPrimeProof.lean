import Langlands.Global.Arithmetic.CyclicNonsplitPrimeStatement
import Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormProof
import Langlands.ClassField.Global.CyclicH2NormIndexComparisonProof
import Langlands.ClassField.Global.CyclicIdeleClassHerbrandAssembly
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.ClassField.Global.IdeleClassNormGaloisProductProof

/-! # Nonsplit finite primes in nontrivial cyclic number-field extensions -/

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension
open Langlands.ClassField.Global

universe u v

/-- A nontrivial cyclic number-field extension has a finite prime of nontrivial
completed degree outside every finite set. -/
theorem cyclicNonsplitPrimeStatement : CyclicNonsplitPrimeStatement.{u, v} := by
  classical
  intro F _ _ E _ _ _ _ _ hdegree S
  by_contra hnone
  have hsplitAt : ∀ (p : HeightOneSpectrum (𝓞 F)), p ∉ S →
      ∀ (q : HeightOneSpectrum (𝓞 E)) (h : q.asIdeal.LiesOver p.asIdeal),
        letI := h
        Module.finrank (p.adicCompletion F) (q.adicCompletion E) = 1 := by
    intro p hp q h
    by_contra hlocal
    exact hnone ⟨p, hp, q, h, hlocal⟩
  have hsurj :=
    AdelicFunctoriality.almostEverywhereSplitIdeleClassNormSurjective F E S hsplitAt
  have hindex :
      (AdelicFunctoriality.ideleClassNorm (K := F) (L := E)).toMonoidHom.range.index =
        1 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.index_top]
  have hdegreeDvd :
      Module.finrank F E ∣ Nat.card (relativeIdeleClassCohomology F E 2 : Type v) :=
    ⟨Nat.card (relativeIdeleClassCohomology F E 1 : Type v),
      (cyclicIdeleClassHerbrandQuotient F E).2.2⟩
  have hcardDvd :=
    cyclicH2NormIndexComparison ideleClassGaloisDescent ideleClassNormGaloisProduct F E
  rw [hindex] at hcardDvd
  have hdegreeOne : Module.finrank F E = 1 :=
    Nat.dvd_one.mp (hdegreeDvd.trans hcardDvd)
  exact (ne_of_gt hdegree) hdegreeOne

end Langlands.Global
