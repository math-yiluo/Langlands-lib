import Langlands.AbelianScheme.Tate.GeometricTorsionPolarizedRank
import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankProof

/-! # Actual torsion cardinality from an ample pullback identity -/

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
/-- The actual ample pullback identity calculates the native multiplication
rank, using the proved general polarized finite-flat rank theorem. -/
theorem multiplicationFinrank_of_amplePullback
    (L : LineBundle B.X.left) (hL : L.IsAmple)
    (hpower : Nonempty
      ((Scheme.Modules.pullback
        (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).obj L.obj ≅
          Langlands.Scheme.Modules.tensorPow L.obj (n * n)))
    (y : B.X.left) :
    (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank y =
      n ^ (2 * g) :=
  multiplicationFinrank_of_polarizedFiniteFlatRank B g hg n hn hnK
    polarizedFiniteFlatRank L hL hpower y

include hg hn hnK in
/-- Actual field torsion has the expected cardinality whenever the actual
ample multiplication-pullback identity is supplied. -/
theorem natCard_level_of_amplePullback
    (L : LineBundle B.X.left) (hL : L.IsAmple)
    (hpower : Nonempty
      ((Scheme.Modules.pullback
        (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).obj L.obj ≅
          Langlands.Scheme.Modules.tensorPow L.obj (n * n))) :
    Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n) =
      n ^ (2 * g) :=
  natCard_level_of_polarizedFiniteFlatRank B g hg n hn hnK
    polarizedFiniteFlatRank L hL hpower

/-- The numerical rank input is proved; symmetric ample existence and
symmetric multiplication pullback remain explicit geometric premises. -/
theorem fieldTorsionCardinality_of_symmetricGeometry
    (hample : GroupScheme.FieldSymmetricAmpleExistenceStatement.{u})
    (hpullback : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u}) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (B : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
      B.HasRelativeDimension g →
        ∀ (n : ℕ), 0 < n → (n : K) ≠ 0 →
          Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 _)) n) =
            n ^ (2 * g) :=
  fieldTorsionCardinality_of_numericalGeometry polarizedFiniteFlatRank hample hpullback

include hg hn hnK in
/-- An enumeration of the existing torsion type from an actual ample
pullback identity. This equivalence asserts no algebraic compatibility. -/
def torsionEquivFinOfAmplePullback
    (L : LineBundle B.X.left) (hL : L.IsAmple)
    (hpower : Nonempty
      ((Scheme.Modules.pullback
        (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).obj L.obj ≅
          Langlands.Scheme.Modules.tensorPow L.obj (n * n))) :
    GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n ≃
      Fin (n ^ (2 * g)) := by
  have hcard := natCard_level_of_amplePullback B g hg n hn hnK L hL hpower
  exact (Nat.equivFinOfCardPos (by rw [hcard]; exact pow_ne_zero _ (Nat.ne_of_gt hn))).trans
    (finCongr hcard)

end Langlands.AbelianScheme.Tate
