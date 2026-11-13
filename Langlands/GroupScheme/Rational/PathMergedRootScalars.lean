import Langlands.GroupScheme.Rational.PathPositiveRootMatrices
import Langlands.GroupScheme.Rational.RootParametrizationScalars
import Langlands.GroupScheme.Rational.AdjacentModifiedData

/-! # Merged-root scalars on normalized path lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

namespace RootParametrization

/-- The rational values of the conjugated map are the actual conjugates. -/
theorem conjugate_rationalPoint {α : p.rootIndex} (z : p.RootParametrization α)
    (n : normalizerPoints p.inclusion) {r : p.rootIndex}
    (hr : p.rootDatum.root r = weylAction p.inclusion n (p.rootDatum.root α)) (c : k) :
    (z.conjugate n hr).rationalPoint c =
      (n : rationalPoints G) * z.rationalPoint c * (n : rationalPoints G)⁻¹ := by
  change VectorGroup.scalarPoint (CommRingCat.of k) _ _ ≫ (z.conjugateHom n).hom.hom = _
  rw [scalarPoint_conjugateHom, constantPoint_self]
  rfl

end RootParametrization

variable {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- The sum of two adjacent simple path roots is the difference of the endpoint weights. -/
theorem adjacentRoot_eq_pathWeight_sub {i : ℕ} (hi : i + 2 ≤ L) {α : p.rootIndex}
    (hr : p.rootDatum.root α = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    p.rootDatum.root α = pathWeight β lam i - pathWeight β lam (i + 2) := by
  rw [hr, root_path_eq_sub (lam := lam), root_path_eq_sub (lam := lam)]
  change (pathWeight β lam i - pathWeight β lam (i + 1)) +
    (pathWeight β lam (i + 1) - pathWeight β lam (i + 2)) = _
  abel

/-- The canonical conjugated adjacent simple-root map is a parametrization of the merged root. -/
def canonicalAdjacentRootMap {i : ℕ} (hi : i + 2 ≤ L) {α : p.rootIndex}
    (hr : p.rootDatum.root α = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) : p.RootParametrization α :=
  (x (β ⟨i + 1, by omega⟩)).toRootParametrization.conjugate
    (x (β ⟨i, by omega⟩)).reflectionRepresentative.normalizerPoint (by
      rw [SimpleReflectionRepresentative.weylAction_normalizerPoint,
        RootPairing.reflection_apply_root, pairing_path_succ hβ hi, neg_one_smul,
        sub_neg_eq_add, add_comm, ← hr])

/-- The canonical conjugated adjacent root adds exactly c times the first endpoint vector. -/
theorem canonicalAdjacentRootMap_normalizedPathVector {i : ℕ} (hi : i + 2 ≤ L)
    {α : p.rootIndex}
    (hr : p.rootDatum.root α = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) (c : k) :
    (ρ.rationalMatrix ((canonicalAdjacentRootMap hβ x hi hr).rationalPoint c) : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
      (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) +
        c • (normalizedPathVector hρ hβ hlam x v₀ i : d → k) := by
  let n := (x (β ⟨i, by omega⟩)).reflectionRepresentative.point
  have hfix : (ρ.rationalMatrix n : Matrix d d k) *ᵥ
      (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
        (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) :=
    canonicalReflection_path_fixes hρ hβ hlam ⟨i, by omega⟩ (x _) (j := i + 2) (by omega)
      (by change i + 2 ≠ i; omega) (by change i + 2 ≠ i + 1; omega)
      (normalizedPathVector hρ hβ hlam x v₀ (i + 2)).2
  have hfixInv : (ρ.rationalMatrix n⁻¹ : Matrix d d k) *ᵥ
      (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
        (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) := by
    calc
      _ = (ρ.rationalMatrix n⁻¹ : Matrix d d k) *ᵥ
          ((ρ.rationalMatrix n : Matrix d d k) *ᵥ
            (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k)) := by rw [hfix]
      _ = _ := by
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, ← map_mul,
          inv_mul_cancel, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hroot := rationalRoot_normalizedPathVector_succ hρ hβ hlam x v₀
    (⟨i + 1, by omega⟩ : Fin L) c
  have hn := canonicalReflection_normalizedPathVector_succ hρ hβ hlam x v₀
    (by omega : i < L)
  change (ρ.rationalMatrix n : Matrix d d k) *ᵥ
    (normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) =
      (normalizedPathVector hρ hβ hlam x v₀ i : d → k) at hn
  change (ρ.rationalMatrix ((x (β ⟨i + 1, by omega⟩)).toRootParametrization.rationalPoint c) :
      Matrix d d k) *ᵥ (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) =
        (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k) +
          c • (normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) at hroot
  rw [canonicalAdjacentRootMap, RootParametrization.conjugate_rationalPoint]
  change (ρ.rationalMatrix (n * _ * n⁻¹) : Matrix d d k) *ᵥ _ = _
  rw [map_mul, map_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hfixInv, hroot, Matrix.mulVec_add, Matrix.mulVec_smul, hfix, hn]

/-- Every supplied merged-root map has a nonzero coefficient in the original field. -/
theorem pathRootScalar_adjacent_ne_zero {i : ℕ} (hi : i + 2 ≤ L) {α : p.rootIndex}
    (z : p.RootParametrization α)
    (hr : p.rootDatum.root α = p.rootDatum.root (β ⟨i, by omega⟩ : p.rootIndex) +
      p.rootDatum.root (β ⟨i + 1, by omega⟩ : p.rootIndex)) :
    pathRootScalar hρ hβ hlam x v₀ hv₀ z ⟨i, by omega⟩ ⟨i + 2, by omega⟩ ≠ 0 := by
  let y := canonicalAdjacentRootMap hβ x hi hr
  have hc := z.rationalPoint_eq_comparisonScalar y 1
  rw [one_mul] at hc
  have ha := congrArg (fun g => (ρ.rationalMatrix g : Matrix d d k) *ᵥ
    (normalizedPathVector hρ hβ hlam x v₀ (i + 2) : d → k)) hc
  rw [rationalPathRoot_normalizedPathVector hρ hβ hlam x v₀ hv₀ z
    ⟨i, by omega⟩ ⟨i + 2, by omega⟩ (by change i < i + 2; omega)
    (adjacentRoot_eq_pathWeight_sub hi hr) 1 ⟨i + 2, by omega⟩] at ha
  dsimp only [y] at ha
  rw [canonicalAdjacentRootMap_normalizedPathVector hρ hβ hlam x v₀ hi hr] at ha
  simp only [ite_true, one_mul] at ha
  have hs := congrArg (fun w : d → k =>
    (normalizedPathBasis hρ hβ hlam x v₀ hv₀).repr w ⟨i, by omega⟩) ha
  rw [← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ ⟨i, by omega⟩,
    ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ ⟨i + 2, by omega⟩] at hs
  simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, smul_eq_mul, ite_true, mul_one] at hs
  have he : pathRootScalar hρ hβ hlam x v₀ hv₀ z ⟨i, by omega⟩ ⟨i + 2, by omega⟩ =
      z.comparisonScalar y := add_left_cancel hs
  rw [he]
  exact z.comparisonScalar_ne_zero y

end Langlands.GroupScheme.SplitPinning
