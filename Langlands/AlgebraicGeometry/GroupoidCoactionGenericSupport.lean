import Langlands.AlgebraicGeometry.GroupoidCoactionGenericEvaluation
import Langlands.AlgebraicGeometry.GroupoidCoactionEvaluation
import Langlands.AlgebraicGeometry.GroupoidCoactionSupportInduction

/-! # Generic support reduction from an effective finite cover -/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P] [Algebra B P] [IsScalarTower B D P]
variable {t : B →+* C} {td : D →+* P}

/-- An effective finite source-cartesian cover supplies the reduced support
step for finite coefficient coactions. -/
theorem hasFiniteSupportVanishingStep_of_cover
    (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
    (e : P ≃ₐ[D] D ⊗[B] C)
    (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
    [Module.FaithfullyFlat (invariantRing td) D]
    (ε : P ≃ₐ[D] D ⊗[invariantRing td] D)
    (hε : ∀ d : D, ε (td d) = (1 : D) ⊗ₜ[invariantRing td] d)
    [IsNoetherianRing B] [IsReduced B] [Nontrivial B] [Module.Finite B D]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B D))) :
    HasFiniteSupportVanishingStep.{u, u} t := by
  classical
  intro M _ _ _ θ
  obtain ⟨q, hq, r, hr, a, I, hI0, hI, hfin, hK, hQ⟩ :=
    exists_genericEvaluation hE hP e ht ε hε hsurj M θ
  let := hfin
  refine ⟨I, hI0, hI, ?_⟩
  intro hvan
  exact oneCohomologyVanishes_of_covering_evaluation e ht hE hP
    (induced td (invariantRing td ⧸ q)) θ ε hε
    (fun i => (1 : D) ⊗ₜ[invariantRing td] a i)
    (fun i => pushforward_induced_one_tmul_mem_invariants hE hP e ht _ (a i))
    (⟨0, hr⟩ : Fin r) I hI hK hQ hvan

end Langlands.AlgebraicGeometry.GroupoidCoaction
