import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Simultaneous normalized p-adic row Fourier cutoffs

This is a proposition target, not a proof. One pair of actual Schwartz--Bruhat
row functions is both a large cutoff, equal to one on a prescribed compact set,
and the plus-sign Fourier preimage of a small cutoff of total mass one, for
every supplied scalar Haar measure that is self-dual for the character.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory

universe u

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the target. -/
theorem rowFourierCutoff_nonarchimedean {K : Type u} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

/-- For a self-dual supplied scalar Haar measure, every compact set of rows and
every open neighbourhood of zero admit one even Fourier pair `(Φ, κ)`: the
plus-sign row transform of `Φ` is `κ`, `Φ` is one on the compact set, `κ` is
supported in the neighbourhood and has integral exactly one for the product
of the supplied measure. This includes dimension zero. -/
def PadicRowFourierCutoffStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) (d : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := rowFourierCutoff_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier), IsSelfDual ψ ν →
    ∀ (C : Set (Fin d → F.Carrier)), IsCompact C →
    ∀ (U : Set (Fin d → F.Carrier)), IsOpen U → (0 : Fin d → F.Carrier) ∈ U →
      ∃ Φ κ : SchwartzBruhat (Fin d → F.Carrier),
        IsRowFourierPair ψ ν Φ κ ∧
        (∀ x ∈ C, Φ x = 1) ∧
        Function.support ⇑κ ⊆ U ∧
        ∫ x, κ x ∂rowMeasure ν d = 1 ∧
        (∀ x, Φ (-x) = Φ x) ∧
        (∀ x, κ (-x) = κ x)

end Langlands.HarmonicAnalysis
