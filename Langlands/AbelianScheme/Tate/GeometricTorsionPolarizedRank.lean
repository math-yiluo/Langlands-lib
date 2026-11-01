import Langlands.AbelianScheme.FieldSymmetricAmpleExistenceStatement
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackStatement
import Langlands.AbelianScheme.Tate.GeometricTorsionNativeRank
import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankStatement

/-! # Actual torsion cardinality from numerical polarized geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] [IsAlgClosed K]
  (B : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ)
  (hg : B.HasRelativeDimension g) (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0)

include hg hn hnK in
/-- An actual ample multiplication-pullback identity gives the numerical
native rank, conditional on the general numerical geometry statement. -/
theorem multiplicationFinrank_of_polarizedFiniteFlatRank
    (hrank : PolarizedFiniteFlatRankStatement.{u})
    (L : LineBundle B.X.left) (hL : L.IsAmple)
    (hpower : Nonempty
      ((Scheme.Modules.pullback
        (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).obj L.obj ≅
          Langlands.Scheme.Modules.tensorPow L.obj (n * n)))
    (y : B.X.left) :
    (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank y =
      n ^ (2 * g) := by
  have := multiplication_etale_of_field B n hnK
  have h := hrank K B.X g hg inferInstance inferInstance
    (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom
    (multiplication_isFinite_of_ne_zero B n hnK) inferInstance
    L hL (n * n) (Nat.mul_pos hn hn) hpower y
  simpa only [← pow_two, ← pow_mul] using h

include hg hn hnK in
/-- The actual torsion count follows from the same actual ample identity
and the explicitly supplied general numerical theorem. -/
theorem natCard_level_of_polarizedFiniteFlatRank
    (hrank : PolarizedFiniteFlatRankStatement.{u})
    (L : LineBundle B.X.left) (hL : L.IsAmple)
    (hpower : Nonempty
      ((Scheme.Modules.pullback
        (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).obj L.obj ≅
          Langlands.Scheme.Modules.tensorPow L.obj (n * n))) :
    Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n) =
      n ^ (2 * g) := by
  let y := η[B.X].left (Classical.arbitrary (Spec (.of K)))
  exact (natCard_level_eq_multiplicationFinrank B n hnK y).trans
    (multiplicationFinrank_of_polarizedFiniteFlatRank B g hg n hn hnK
      hrank L hL hpower y)

/-- General numerical rank, symmetric ample existence and symmetric
multiplication pullback imply the actual field-level numerical torsion
formula. All three unproved geometric inputs remain explicit. -/
theorem fieldTorsionCardinality_of_numericalGeometry
    (hrank : PolarizedFiniteFlatRankStatement.{u})
    (hample : GroupScheme.FieldSymmetricAmpleExistenceStatement.{u})
    (hpullback : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u}) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (B : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
      B.HasRelativeDimension g →
        ∀ (n : ℕ), 0 < n → (n : K) ≠ 0 →
          Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 _)) n) =
            n ^ (2 * g) := by
  intro K _ _ B g hg n hn hnK
  obtain ⟨L, hL, hsym⟩ :=
    hample K B.toGrp inferInstance inferInstance inferInstance
  exact natCard_level_of_polarizedFiniteFlatRank B g hg n hn hnK hrank L hL
    (hpullback K B.toGrp inferInstance inferInstance inferInstance L hsym n hn)

include hg hn hnK in
/-- A finite enumeration of actual torsion, conditional on the three geometric
inputs. This is an equivalence of types and asserts no algebraic compatibility. -/
def torsionEquivFinOfNumericalGeometry
    (hrank : PolarizedFiniteFlatRankStatement.{u})
    (hample : GroupScheme.FieldSymmetricAmpleExistenceStatement.{u})
    (hpullback : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u}) :
    GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n ≃
      Fin (n ^ (2 * g)) := by
  have hcard :=
    fieldTorsionCardinality_of_numericalGeometry hrank hample hpullback K B g hg n hn hnK
  exact (Nat.equivFinOfCardPos (by rw [hcard]; exact pow_ne_zero _ (Nat.ne_of_gt hn))).trans
    (finCongr hcard)

end Langlands.AbelianScheme.Tate
