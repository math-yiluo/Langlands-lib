import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Multiplicity freeness of products of distinct supercuspidal data

Zelevinsky 1980, Proposition 2.1(c), expressed by an actual finite composition
series of upper normalized induction with pairwise inequivalent graded factors.
This is a proposition definition, not a proof.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Ze80 Proposition 2.1(c): the upper normalized product of pairwise distinct
irreducible supercuspidal data has an actual finite composition series in which
no two graded factors are equivalent. Distinctness compares rank-indexed
isomorphism classes. The field and factor-carrier universes are independent. -/
def DistinctCuspidalProductMultiplicityFree : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
      Function.Injective (fun i : Fin B.length =>
        (⟨B.size i, (A i).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d))) →
      let P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
        (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)
      ∃ (m : ℕ) (s : ObjectRepFiltration P.obj m),
        s.HasSimpleFactors ∧
          ∀ i j : Fin m,
            Nonempty ((s.gradedRepresentation i).ρ.Equiv
              (s.gradedRepresentation j).ρ) → i = j

end Langlands.Classification
