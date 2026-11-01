import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Induction.BlockFactors

/-! Actual integral Jacquet words of constituents of cuspidal products. -/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- An irreducible actual constituent of an integral cuspidal product has an
actual Jacquet word that permutes the original integer labels. -/
def IntegralCuspidalConstituentWord : Prop :=
  letI := T.topology
  ∀ (m n : ℕ), 0 < n →
    ∀ (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
      (B : BlockShape n)
      (C : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i))
      (e : Fin B.length → ℤ),
      (∀ i : Fin B.length,
        (⟨B.size i, (C i).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨m, T.supercuspidalClassRealPowerTwist m (e i : ℝ) A.isoClass⟩) →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        π.IsIrreducible →
        SmoothRep.IsSubquotient π
          ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)) →
        ∃ w : List ℤ, IntegralCuspidalJacquetWord F T m n A π w ∧
          w.Perm (List.ofFn e)

end Langlands.Classification
