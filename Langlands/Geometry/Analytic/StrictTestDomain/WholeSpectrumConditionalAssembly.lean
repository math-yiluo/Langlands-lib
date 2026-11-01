import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumLocalizationAdapter
import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumRefinementAdapter
import Langlands.Geometry.Analytic.StrictTestDomain.WholeSpectrumRationalGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalRefinementStatement
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalRefinementProof
import Langlands.Geometry.Analytic.StrictTestDomain.NontrivialStandardRationalGluingStatement

/-! # Conditional whole-spectrum assembly

This file records the standard-cover input explicitly.
`WholeSpectrumRationalGluingProof` supplies its published proof.
-/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

/-- Formal assembly from two named published propositions.
This conditional theorem is not the final exact-target proof. -/
theorem wholeSpectrumRationalGluing_of_standard_inputs
    (href : FiniteRationalRefinementStatement.{u})
    (hstd : NontrivialStandardRationalGluingStatement.{u}) :
    WholeSpectrumRationalGluingStatement.{u} := by
  classical
  intro K _ _ _ P I _ D hc s hs
  by_cases hI : Nonempty I
  · by_cases hK : ∃ c : K, 1 < ‖c‖
    · obtain ⟨n, f, hf, hi⟩ := href K P I D hc
      let k : Fin n → I := fun j => (hi j).choose
      let inc (j : Fin n) : standardRational f hf j ⟶ D (k j) :=
        ⟨(hi j).choose_spec⟩
      exact existsUnique_whole_gluing_of_standard_refinement
        (hstd K hK) D f hf k inc s hs
    · have hbound : ∀ c : K, ‖c‖ ≤ 1 := fun c =>
        le_of_not_gt (fun hc => hK ⟨c, hc⟩)
      exact existsUnique_whole_gluing_of_trivial_scalar_norm hbound D hc s hs
  · let : IsEmpty I := not_nonempty_iff.mp hI
    exact existsUnique_whole_gluing_empty D hc s

/-- Use the published finite refinement proof, leaving only nontrivial
standard descent as an explicit premise. -/
theorem wholeSpectrumRationalGluing_of_nontrivial_standard
    (hstd : NontrivialStandardRationalGluingStatement.{u}) :
    WholeSpectrumRationalGluingStatement.{u} :=
  wholeSpectrumRationalGluing_of_standard_inputs finiteRationalRefinement hstd

end Langlands.Analytic.StrictTestDomain
