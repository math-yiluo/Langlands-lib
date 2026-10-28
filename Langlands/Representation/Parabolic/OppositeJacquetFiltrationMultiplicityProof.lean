import Langlands.Representation.Parabolic.OppositeJacquetFiltrationMultiplicityStatement
import Langlands.Representation.Parabolic.OppositeJacquetFiltrationGradedProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

noncomputable section

open scoped BigOperators

namespace Langlands.Parabolic.OppositeFiltrationMultiplicityProof

universe uK uG uA uB uW

/-- Construct finite-series witnesses on either side of a supplied graded
equivalence family, using the actual ambient filtration. -/
private theorem multiplicity_iff_of_graded_equivs
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    (A : Rep.{uA} k G) (τ : Rep.{uW} k G) {l : ℕ}
    (s : ObjectRepFiltration A l) (pieces : Fin l → Rep.{uB} k G)
    (h : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv (pieces i).ρ))
    (m : ℕ) :
    HasJordanHolderMultiplicity A τ m ↔
      ∃ counts : Fin l → ℕ,
        (∀ i, HasJordanHolderMultiplicity (pieces i) τ (counts i)) ∧
        (∑ i : Fin l, counts i) = m := by
  classical
  constructor
  · rintro ⟨N, t, ht, hct⟩
    obtain ⟨lengths, counts, H, _, hc⟩ :=
      jordanHolderFiltrationDecomposition k G A τ N m l
        ⟨t, ht⟩ ⟨N, t, ht, hct⟩ s
    refine ⟨counts, ?_, hc⟩
    intro i
    obtain ⟨e⟩ := h i
    obtain ⟨r, hr, hcr⟩ := H i
    exact (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation i)
      (pieces i) τ τ e (Representation.Equiv.refl _) (counts i)).mp
      ⟨lengths i, r, hr, hcr⟩
  · rintro ⟨counts, H, hc⟩
    have H' : ∀ i : Fin l, HasJordanHolderMultiplicity
        (s.gradedRepresentation i) τ (counts i) := by
      intro i
      obtain ⟨e⟩ := h i
      exact (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation i)
        (pieces i) τ τ e (Representation.Equiv.refl _) (counts i)).mpr (H i)
    choose lengths t ht hct using H'
    obtain ⟨r, hr, hcr⟩ :=
      jordanHolderFiltrationAdditivity k G A τ l s lengths counts
        (fun i => ⟨t i, ht i, hct i⟩)
    exact ⟨∑ i : Fin l, lengths i, r, hr, hcr.trans hc⟩

end Langlands.Parabolic.OppositeFiltrationMultiplicityProof

namespace Langlands.Parabolic

open GeneralLinear Geometric OppositeFiltrationMultiplicityProof

universe uF uV uW

/-- Actual finite-series multiplicities add and decompose across the fixed
refined and composed opposite Jacquet image filtrations. -/
theorem normalizedOppositeJacquetFiltrationMultiplicity :
    NormalizedOppositeJacquetFiltrationMultiplicityStatement.{uF, uV, uW} := by
  intro p hp F T n B S
  obtain ⟨hRefined, hComposed⟩ :=
    normalizedOppositeJacquetFiltrationGraded.{uF, uV} p F T n B S
  constructor
  · let := T.topology
    intro V hV hMV ρ hρ l s τ m
    exact multiplicity_iff_of_graded_equivs
      (Rep.of (T.normalizedRefinedOppositeJacquet B S ρ)) τ
      (T.normalizedRefinedOppositeJacquetFiltration B S ρ s)
      (fun i => Rep.of (T.normalizedRefinedOppositeJacquet B S
        (s.gradedRepresentation i).ρ))
      (hRefined V ρ hρ l s) m
  · let := T.topology
    intro V hV hMV ρ hρ l s τ m
    exact multiplicity_iff_of_graded_equivs
      (Rep.of (T.normalizedComposedOppositeJacquet B S ρ)) τ
      (T.normalizedComposedOppositeJacquetFiltration B S ρ s)
      (fun i => Rep.of (T.normalizedComposedOppositeJacquet B S
        (s.gradedRepresentation i).ρ))
      (hComposed V ρ hρ l s) m

end Langlands.Parabolic
