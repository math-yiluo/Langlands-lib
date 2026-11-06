import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.IteratedLaurentIdealDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictScalarIdealDescentStatement

/-! # The strict rational ideal correspondence -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Every finite strict rational point cover has effective compatible ideals,
by the actual binary Laurent theorem and the completed covering reductions. -/
theorem idealCoverDescent_finiteRational (hK : ∃ c : K, 1 < ‖c‖)
    {n : ℕ} (D : Fin n → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) : IdealCoverDescent D :=
  idealCoverDescent_finiteRational_of_inputs hK
    (fun _ f => binaryIdealDescent_laurent hK f)
    (fun _ _ f hf hu => idealCoverDescent_allUnitStandardRational hK f hf hu) D hD

/-- Global ideals correspond, with their inclusion order, to compatible local
ideal families on an actual finite strict rational point cover. The inverse
is exactly the intersection of inverse images under the original base maps. -/
def rationalIdealOrderIso (hK : ∃ c : K, 1 < ‖c‖)
    {n : ℕ} (D : Fin n → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) :
    Ideal P ≃o {I : ∀ i, Ideal (D i).algebra // CompatibleIdealSections D I} where
  toFun J := ⟨fun i => (D i).baseMap.closedIdealMap J, CompatibleIdealSections.of_base D J⟩
  invFun I := idealSectionContraction D I.val
  left_inv J := by
    ext a
    rw [mem_idealSectionContraction]
    exact ⟨idealCoverSeparated_of_covers hK D hD J a,
      fun ha i => (D i).baseMap.mem_closedIdealMap ha⟩
  right_inv I := Subtype.ext (funext (idealCoverDescent_finiteRational hK D hD I.val I.property))
  map_rel_iff' := by
    intro J H
    constructor
    · intro h a ha
      apply idealCoverSeparated_of_covers hK D hD H a
      intro i
      exact h i ((D i).baseMap.mem_closedIdealMap ha)
    · intro h i
      exact (D i).baseMap.closedIdealMap_mono h

/-- The exact strict rational ideal-effectiveness proposition, with no binary,
all-unit, module-descent or reverse-containment premises remaining. -/
theorem strictRationalIdealEffectiveness :
    PresentedAffinoidAlgebra.Domain.FiniteCover.StrictRationalIdealEffectivenessStatement.{u} := by
  intro K _ _ _ hK P n D hD I _ hI
  exact idealCoverDescent_finiteRational hK D hD I hI

end Langlands.Analytic.StrictTestDomain
