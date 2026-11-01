import Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.Representation.Aubert.AlternatingOperator

/-! The exact finite-length Grothendieck form of the actual geometric lemma. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Uniform actual geometric pieces compute normalized Jacquet restriction after
normalized induction on every actual finite-length smooth class. All refinements,
intersection equalities, enumeration and piece lengths are conclusions. -/
def GeometricLemmaGrothendieckStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    ∃ (S : MinimalRepresentatives B C → BlockRefinement B)
      (R : MinimalRepresentatives B C → BlockRefinement C),
      ∃ (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S w))
        (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R w)),
        ∃ (m : ℕ) (e : Fin m ≃ MinimalRepresentatives B C),
          ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
            (hA : A.HasFiniteLength),
            ∃ hP : ∀ i : Fin m,
              ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
                F T B C (e i).val (S (e i)) (R (e i))
                (hS (e i)).2.1 (hR (e i)).2.1).obj A).HasFiniteLength,
              Parabolic.normalizedJacquetK0.{uF, uV} F T C
                  (Parabolic.normalizedInductionK0.{uF, uV} F T B
                    (B.finiteLengthClass F.Carrier A hA)) =
                ∑ i : Fin m, C.finiteLengthClass F.Carrier
                  ((CuspidalSupport.geometricPieceSmoothFunctor.{uF, max uF uV}
                    F T B C (e i).val (S (e i)) (R (e i))
                    (hS (e i)).2.1 (hR (e i)).2.1).obj A) (hP i)

end Langlands.Geometric
