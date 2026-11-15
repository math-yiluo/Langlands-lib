import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement
import Langlands.CommutativeAlgebra.FiniteTypeIntGRingProof
import Langlands.CommutativeAlgebra.Popescu.PopescuFactorizationProof
import Langlands.CommutativeAlgebra.SmoothEtaleCompletionApproximationProof
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing

/-! # Etale approximation over finite-type integer algebras: proof -/

universe u

namespace Langlands.CommutativeAlgebra

/-- A Noetherian local ring whose canonical map to its adic completion is regular
has finite-order approximation in etale neighbourhoods. Popescu factorization
reduces to a smooth source, and the smooth-source theorem finishes. -/
theorem etaleCompletionApproximation_of_regularAlgebra_completion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : RegularAlgebra R
      (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    EtaleCompletionApproximation R := by
  let I := IsLocalRing.maximalIdeal R
  let : IsNoetherianRing (AdicCompletion I R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  intro C _ _ _ f N
  obtain ⟨B, _, _, hB, g, h, hf⟩ :=
    Popescu.popescuFactorization R (AdicCompletion I R) hR C f
  let : Algebra.Smooth R B := hB
  obtain ⟨E, _, _, hE, gE, ι, hEcomp⟩ :=
    smoothEtaleCompletionApproximation R B h N
  refine ⟨E, inferInstance, inferInstance, hE, gE.comp g, ι, ?_⟩
  ext x
  exact (AlgHom.congr_fun hEcomp (g x)).trans
    (congrArg (AdicCompletion.evalₐ I N) (AlgHom.congr_fun hf x))

/-- Every maximal localization of a finite-type integer algebra has finite-order
approximation in etale neighbourhoods for maps into its completion. -/
theorem finiteTypeIntEtaleCompletionApproximation :
    FiniteTypeIntEtaleCompletionApproximationStatement.{u} := by
  intro S _ _ 𝔪 _
  let : IsNoetherianRing S := (finiteTypeIntGRing S).isNoetherianRing
  exact etaleCompletionApproximation_of_regularAlgebra_completion
    (Localization.AtPrime 𝔪) ((finiteTypeIntGRing S).regularAlgebra_completion 𝔪)

end Langlands.CommutativeAlgebra
