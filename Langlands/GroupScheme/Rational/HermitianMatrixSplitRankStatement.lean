import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Split rank from an actual all-test Hermitian matrix presentation

This module states the equality of split rank and the maximal dimension of
actual totally isotropic submodules. The presentation is supplied on every
test scheme, and the statement makes no classification assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a group scheme supplied with an actual all-test determinant-one
Hermitian matrix presentation, the split rank is the attained maximum of the
dimensions of actual totally isotropic submodules. The pairing is linear in
the first vector and conjugate-linear in the second. -/
def HermitianMatrixSplitRankStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
    (n : ℕ), 2 ≤ n →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom]
      (J : Matrix.GeneralLinearGroup (Fin (n + 1)) L),
      ((J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
        (SU3Root.fieldInvolution K L).bar).transpose =
        (J : Matrix (Fin (n + 1)) (Fin (n + 1)) L) →
      ∀ (ρ : ∀ T : Over (Spec (CommRingCat.of K)),
        (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin (n + 1))
          (SpecialLinear.WeilRoot.tensorAlgebra K L T)),
        (∀ T, Function.Injective (ρ T)) →
        (∀ (T : Over (Spec (CommRingCat.of K)))
          (g : Matrix.GeneralLinearGroup (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)),
          (∃ x : T ⟶ G.X, ρ T x = g) ↔
            ((g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
                (J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
                  (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
                (g : Matrix (Fin (n + 1)) (Fin (n + 1))
                  (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
              (J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
                (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
              Matrix.GeneralLinearGroup.det g = 1) →
        (∀ {T T' : Over (Spec (CommRingCat.of K))}
          (a : T' ⟶ T) (x : T ⟶ G.X),
          (ρ T' (a ≫ x) : Matrix (Fin (n + 1)) (Fin (n + 1))
              (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
            (ρ T x : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SpecialLinear.WeilRoot.tensorMap K L a)) →
        (∃ W : Submodule L (Fin (n + 1) → L),
          (∀ a b : W, dotProduct (fun i => (SU3Root.fieldInvolution K L).bar (b.val i))
            ((J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).mulVec a.val) = 0) ∧
          (Module.finrank L W : ℕ∞) = splitRank G) ∧
        ∀ W : Submodule L (Fin (n + 1) → L),
          (∀ a b : W, dotProduct (fun i => (SU3Root.fieldInvolution K L).bar (b.val i))
            ((J : Matrix (Fin (n + 1)) (Fin (n + 1)) L).mulVec a.val) = 0) →
          (Module.finrank L W : ℕ∞) ≤ splitRank G

end Langlands.GroupScheme
