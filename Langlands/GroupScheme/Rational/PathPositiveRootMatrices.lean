import Langlands.GroupScheme.Rational.PathRootMatrices

/-! # Positive-root matrices on normalized path lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}
  (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) (hv₀ : v₀ ≠ 0)

/-- The coefficient of a supplied root map between two normalized path lines. -/
def pathRootScalar {α : p.rootIndex} (z : p.RootParametrization α)
    (i l : Fin (L + 1)) : k :=
  (normalizedPathBasis hρ hβ hlam x v₀ hv₀).repr
    (dividedPower (ρ.restrict z.hom) 1
      (normalizedPathVector hρ hβ hlam x v₀ l : d → k)) i

/-- The only possible first divided power between the two path lines is its scalar coefficient. -/
theorem pathRoot_dividedPower_normalizedPathVector {α : p.rootIndex}
    (z : p.RootParametrization α) (i l : Fin (L + 1)) (hil : i < l)
    (hr : p.rootDatum.root α = pathWeight β lam i - pathWeight β lam l) :
    dividedPower (ρ.restrict z.hom) 1
        (normalizedPathVector hρ hβ hlam x v₀ l : d → k) =
      pathRootScalar hρ hβ hlam x v₀ hv₀ z i l •
        (normalizedPathVector hρ hβ hlam x v₀ i : d → k) := by
  have hx := z.torus_equivariant
  rw [hr] at hx
  have hmem := pathRootMap_dividedPower_one_mem hβ hil (by omega) hx
    (normalizedPathVector hρ hβ hlam x v₀ l).2
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_pathWeightSpace hρ hβ hlam (by omega : (i : ℕ) ≤ L))
    (x := normalizedPathVector hρ hβ hlam x v₀ i)
    (fun he => normalizedPathVector_ne_zero hρ hβ hlam x v₀ hv₀
      (by omega : (i : ℕ) ≤ L) (congrArg Subtype.val he))
    ⟨_, hmem⟩
  have hc' := congrArg Subtype.val hc
  change c • (normalizedPathVector hρ hβ hlam x v₀ i : d → k) =
    dividedPower (ρ.restrict z.hom) 1
      (normalizedPathVector hρ hβ hlam x v₀ l : d → k) at hc'
  have hcoef : pathRootScalar hρ hβ hlam x v₀ hv₀ z i l = c := by
    unfold pathRootScalar
    rw [← hc', ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i]
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply,
      smul_eq_mul, ite_true, mul_one]
  rw [hcoef]
  exact hc'.symm

/-- A root point of weight epsilon_i - epsilon_l adds its scalar multiple only in column l. -/
theorem rationalPathRoot_normalizedPathVector {α : p.rootIndex}
    (z : p.RootParametrization α) (i l : Fin (L + 1)) (hil : i < l)
    (hr : p.rootDatum.root α = pathWeight β lam i - pathWeight β lam l)
    (c : k) (j : Fin (L + 1)) :
    (ρ.rationalMatrix (z.rationalPoint c) : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ j : d → k) =
      (normalizedPathVector hρ hβ hlam x v₀ j : d → k) +
        (if j = l then c * pathRootScalar hρ hβ hlam x v₀ hv₀ z i l else 0) •
          (normalizedPathVector hρ hβ hlam x v₀ i : d → k) := by
  have hx := z.torus_equivariant
  rw [hr] at hx
  have hhi : ∀ m, 2 ≤ m → dividedPower (ρ.restrict z.hom) m = 0 :=
    fun m hm => pathRootMap_dividedPower_eq_zero hρ hβ hlam hil (by omega) hx hm
  rw [z.rationalMatrix_eq_one_add ρ hhi c, one_add_smul_mulVec]
  by_cases hj : j = l
  · subst j
    rw [pathRoot_dividedPower_normalizedPathVector hρ hβ hlam x v₀ hv₀ z i l hil hr]
    simp only [ite_true, mul_smul]
  · have hz := pathRootMap_dividedPower_one_eq_zero hρ hβ hlam hil (by omega) hx
      (j := j.val) (by omega) (fun h => hj (Fin.ext h))
      (normalizedPathVector hρ hβ hlam x v₀ j).2
    rw [hz, ite_eq_right hj, zero_smul, smul_zero]

/-- The full matrix of a supplied positive path-root map in normalized coordinates. -/
theorem normalizedPathMatrix_pathRoot {α : p.rootIndex}
    (z : p.RootParametrization α) (i l : Fin (L + 1)) (hil : i < l)
    (hr : p.rootDatum.root α = pathWeight β lam i - pathWeight β lam l) (c : k) :
    normalizedPathMatrix hρ hβ hlam x v₀ hv₀ (z.rationalPoint c) =
      1 + Matrix.single i l (c * pathRootScalar hρ hβ hlam x v₀ hv₀ z i l) := by
  let B := normalizedPathBasis hρ hβ hlam x v₀ hv₀
  apply Matrix.ext
  intro a b
  rw [normalizedPathMatrix_apply hρ hβ hlam x v₀ hv₀,
    rationalPathRoot_normalizedPathVector hρ hβ hlam x v₀ hv₀ z i l hil hr]
  rw [← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ b,
    ← normalizedPathBasis_apply hρ hβ hlam x v₀ hv₀ i]
  change B.repr (B b + _ • B i) a = _
  simp only [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hb : b = l <;> by_cases ha : a = i
  all_goals simp only [hb, ha, eq_comm, ite_true, ite_false, mul_one, zero_mul,
    and_true, true_and]
  all_goals simp_all only [eq_comm, ite_false, mul_zero, add_zero, and_self]

end Langlands.GroupScheme.SplitPinning
