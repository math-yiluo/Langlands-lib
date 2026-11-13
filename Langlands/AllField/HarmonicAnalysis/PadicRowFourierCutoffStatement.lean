import Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Simultaneous normalized local-field row Fourier cutoffs

This is a proposition target, not a proof. One pair of actual Schwartz--Bruhat
row functions is both a large cutoff, equal to one on a prescribed compact set,
and the plus-sign Fourier preimage of a small cutoff of total mass one, for
every supplied scalar Haar measure that is self-dual for the character.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierCutoffStatement
open Langlands.AllField.HarmonicAnalysis

open MeasureTheory

universe u

/-- For a self-dual supplied scalar Haar measure, every compact set of rows and
every open neighbourhood of zero admit one even Fourier pair `(Φ, κ)`: the
plus-sign row transform of `Φ` is `κ`, `Φ` is one on the compact set, `κ` is
supported in the neighbourhood and has integral exactly one for the product
of the supplied measure. This includes dimension zero. -/
def PadicRowFourierCutoffStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) (d : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := rowFourierCutoff_nonarchimedean (K := F)
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
    ∀ (C : Set (Fin d → F)), IsCompact C →
    ∀ (U : Set (Fin d → F)), IsOpen U → (0 : Fin d → F) ∈ U →
      ∃ Φ κ : SchwartzBruhat (Fin d → F),
        IsRowFourierPair ψ ν Φ κ ∧
        (∀ x ∈ C, Φ x = 1) ∧
        Function.support ⇑κ ⊆ U ∧
        ∫ x, κ x ∂rowMeasure ν d = 1 ∧
        (∀ x, Φ (-x) = Φ x) ∧
        (∀ x, κ (-x) = κ x)

end Langlands.AllField.HarmonicAnalysis
