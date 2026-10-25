import Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeStatement
import Langlands.Global.Arithmetic.CyclicPrimePowerLocalDegreeReductionProof
import Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof

namespace Langlands.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdelicFunctoriality.FiniteExtension

universe u v

/-- A cyclic prime-power number-field extension has a finite prime of full
completed degree outside every finite set. -/
theorem cyclicPrimePowerLocalDegreeStatement :
    CyclicPrimePowerLocalDegreeStatement.{u,v} := by
  intro F _ _ E _ _ _ _ _ ℓ r hℓ hr hdeg S
  obtain ⟨K, hGalois, hCyclic, hKdeg, hTest⟩ :=
    cyclicPrimePowerLocalDegreeReductionStatement F E ℓ r hℓ hr hdeg
  let := hGalois
  let := hCyclic
  have hKnontrivial : 1 < Module.finrank F K := by
    rw [hKdeg]
    exact hℓ.one_lt
  obtain ⟨p, hp, q, hqp, hlocal⟩ :=
    cyclicNonsplitPrimeStatement F K hKnontrivial S
  obtain ⟨w, _, hwp, hfull⟩ := hTest p q hqp hlocal
  exact ⟨p, hp, w, hwp, hfull⟩

end Langlands.Global
