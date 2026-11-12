import Langlands.GroupScheme.Rational.PathReflectionScalars
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # The normalized path basis and rational representation matrices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

include hv₀ in
/-- The normalized path vectors form a linearly independent family. -/
theorem linearIndependent_normalizedPathVector :
    LinearIndependent k (fun j : Fin (L + 1) =>
      (normalizedPathVector hρ hβ hlam x v₀ j : d → k)) := by
  have hind : iSupIndep (fun j : Fin (L + 1) =>
      p.representationWeightSpace ρ (pathWeight β lam j)) :=
    (iSupIndep_representationWeightSpace ρ).comp fun i j h =>
      Fin.ext (pathWeight_injOn hβ hlam (by omega) (by omega) h)
  exact iSupIndep.linearIndependent _ hind
    (fun j => (normalizedPathVector hρ hβ hlam x v₀ j).2)
    (fun j => normalizedPathVector_ne_zero hρ hβ hlam x v₀ hv₀ (by omega))

/-- The path basis whose consecutive vectors are normalized by the supplied simple-root maps. -/
def normalizedPathBasis : Module.Basis (Fin (L + 1)) k (d → k) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_normalizedPathVector hρ hβ hlam x v₀ hv₀)
    (by rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card,
      card_eq_of_isHighestWeight hρ hβ hlam])

@[simp] theorem normalizedPathBasis_apply (j : Fin (L + 1)) :
    normalizedPathBasis hρ hβ hlam x v₀ hv₀ j =
      (normalizedPathVector hρ hβ hlam x v₀ j : d → k) :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) j

/-- The matrix of a rational representation point in the normalized path basis. -/
def normalizedPathMatrix : rationalPoints G →* Matrix (Fin (L + 1)) (Fin (L + 1)) k :=
  (LinearMap.toMatrixAlgEquiv (normalizedPathBasis hρ hβ hlam x v₀ hv₀)).toMonoidHom.comp
    (Matrix.toLinAlgEquiv' : Matrix d d k ≃ₐ[k] Module.End k (d → k)).toMonoidHom |>.comp
      (Units.coeHom _ |>.comp ρ.rationalMatrix)

/-- The matrix coefficient is the indicated coordinate of the action on a normalized vector. -/
theorem normalizedPathMatrix_apply (g : rationalPoints G) (i j : Fin (L + 1)) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ g i j =
      (normalizedPathBasis hρ hβ hlam x v₀ hv₀).repr
        ((ρ.rationalMatrix g : Matrix d d k) *ᵥ
          (normalizedPathVector hρ hβ hlam x v₀ j : d → k)) i := by
  change LinearMap.toMatrixAlgEquiv (normalizedPathBasis hρ hβ hlam x v₀ hv₀)
    (Matrix.toLin' (ρ.rationalMatrix g : Matrix d d k)) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.toLin'_apply, normalizedPathBasis_apply]

/-- Changing to the normalized path basis preserves the characteristic polynomial. -/
theorem charpoly_normalizedPathMatrix (g : rationalPoints G) :
    (normalizedPathMatrix hρ hβ hlam x v₀ hv₀ g).charpoly =
      (ρ.rationalMatrix g : Matrix d d k).charpoly := by
  change (LinearMap.toMatrix _ _ (Matrix.toLin' _)).charpoly = _
  rw [LinearMap.charpoly_toMatrix, Matrix.charpoly_toLin']
  rfl

end Langlands.GroupScheme.SplitPinning
