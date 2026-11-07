import Langlands.GroupScheme.Rational.RootActionWeights
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights
import Langlands.GroupScheme.Rational.DominantHighestWeight
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Closed weight paths for actual Steinberg coefficient matrices -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators Matrix

namespace Langlands.LinearAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem sum_closedPath_differences (r : ℕ) (v : Fin (r + 1) → M) :
    ∑ j : Fin r, (v j.castSucc - v j.succ) = v 0 - v (Fin.last r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun j => v j.succ)
    simp only [Fin.succ_castSucc] at ht
    rw [ht]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    abel

/-- A closed path taking one step in each independent direction is constant,
and every scalar step coefficient is zero. -/
theorem closedIndependentPath_constant {r : ℕ} (a : Fin r → M)
    (ha : LinearIndependent R a) (v : Fin (r + 1) → M) (c : Fin r → R)
    (hstep : ∀ j, v j.castSucc - v j.succ = c j • a j)
    (hclose : v 0 = v (Fin.last r)) :
    (∀ j, c j = 0) ∧ ∀ j, v j = v 0 := by
  have hc : ∀ j, c j = 0 := by
    apply Fintype.linearIndependent_iff.mp ha
    simp_rw [← hstep]
    rw [sum_closedPath_differences, hclose, sub_self]
  refine ⟨hc, ?_⟩
  have hs (j : Fin r) : v j.castSucc = v j.succ := by
    apply sub_eq_zero.mp
    rw [hstep, hc, zero_smul]
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih => exact (hs j).symm.trans ih

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The weight of a degree-m coefficient of a root factor followed by its
supplied simple-reflection representative. -/
def coefficientWeightStep (a : p.base.support) (m : ℕ)
    (lam : characterLattice p.torus) : characterLattice p.torus :=
  p.rootDatum.reflection a lam + m • p.rootDatum.root a

/-- Suffix weights in the original order of the supplied simple-root factors. -/
def coefficientWeightPath :
    (r : ℕ) → (Fin r → p.base.support) → (Fin r → ℕ) →
      characterLattice p.torus → Fin (r + 1) → characterLattice p.torus
  | 0, _, _, lam => fun _ => lam
  | r + 1, a, m, lam =>
      Fin.cons
        (p.coefficientWeightStep (a 0) (m 0)
          (coefficientWeightPath r (fun j => a j.succ) (fun j => m j.succ) lam 0))
        (coefficientWeightPath r (fun j => a j.succ) (fun j => m j.succ) lam)

@[simp] theorem coefficientWeightPath_last (r : ℕ) (a : Fin r → p.base.support)
    (m : Fin r → ℕ) (lam : characterLattice p.torus) :
    p.coefficientWeightPath r a m lam (Fin.last r) = lam := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [coefficientWeightPath, ← Fin.succ_last, Fin.cons_succ] using
      ih (fun j => a j.succ) (fun j => m j.succ)

theorem coefficientWeightPath_step (r : ℕ) (a : Fin r → p.base.support)
    (m : Fin r → ℕ) (lam : characterLattice p.torus) (j : Fin r) :
    p.coefficientWeightPath r a m lam j.castSucc =
      p.coefficientWeightStep (a j) (m j) (p.coefficientWeightPath r a m lam j.succ) := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simpa only [← Fin.succ_castSucc, coefficientWeightPath, Fin.cons_succ] using
        ih (fun i => a i.succ) (fun i => m i.succ) j

theorem coefficientWeightStep_eq_self_of_pairing (a : p.base.support) (m : ℕ)
    (lam : characterLattice p.torus)
    (hm : (m : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot a)) :
    p.coefficientWeightStep a m lam = lam := by
  rw [coefficientWeightStep, p.rootDatum.reflection_apply]
  change lam - (p.rootDatum.toLinearMap lam (p.rootDatum.coroot a)) •
    p.rootDatum.root a + m • p.rootDatum.root a = lam
  rw [← hm]
  module

theorem coefficientWeightPath_zero_of_pairings (r : ℕ) (a : Fin r → p.base.support)
    (m : Fin r → ℕ) (lam : characterLattice p.torus)
    (hm : ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (a j))) :
    p.coefficientWeightPath r a m lam 0 = lam := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change p.coefficientWeightStep (a 0) (m 0)
      (p.coefficientWeightPath r (fun j => a j.succ) (fun j => m j.succ) lam 0) = lam
    rw [ih (fun j => a j.succ) (fun j => m j.succ) (fun j => hm j.succ)]
    exact p.coefficientWeightStep_eq_self_of_pairing _ _ _ (hm 0)

variable {p} {r : ℕ} (e : Fin r ≃ p.base.support)

/-- A cyclic coefficient path through each simple root once is constant, and
each degree is the integral simple-coroot pairing of that single weight. -/
theorem coefficientWeightPath_constant_of_closed (m : Fin r → ℕ)
    (lam : characterLattice p.torus)
    (hclose : p.coefficientWeightPath r e m lam 0 = lam) :
    (∀ j, p.coefficientWeightPath r e m lam j = lam) ∧
      ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j)) := by
  let v := p.coefficientWeightPath r e m lam
  have hstep (j : Fin r) : v j.castSucc - v j.succ =
      ((m j : ℤ) - p.rootDatum.toLinearMap (v j.succ)
        (p.rootDatum.coroot (e j))) • p.rootDatum.root (e j) := by
    dsimp only [v]
    rw [coefficientWeightPath_step, coefficientWeightStep, p.rootDatum.reflection_apply]
    change (v j.succ - (p.rootDatum.toLinearMap (v j.succ)
      (p.rootDatum.coroot (e j))) • p.rootDatum.root (e j) +
      m j • p.rootDatum.root (e j)) - v j.succ = _
    module
  have hclosed : v 0 = v (Fin.last r) := by
    simpa only [v, coefficientWeightPath_last] using hclose
  obtain ⟨hc, hv⟩ := Langlands.LinearAlgebra.closedIndependentPath_constant
    (fun j => p.rootDatum.root (e j)) (p.base.linearIndepOn_root.comp e e.injective)
    v _ hstep hclosed
  have hconst (j) : v j = lam := (hv j).trans hclose
  refine ⟨hconst, ?_⟩
  intro j
  have hj := hc j
  rw [hconst] at hj
  exact sub_eq_zero.mp hj

/-- Closing the actual coefficient weight path is equivalent to the prescribed
simple-coroot exponents. -/
theorem coefficientWeightPath_closed_iff (m : Fin r → ℕ)
    (lam : characterLattice p.torus) :
    p.coefficientWeightPath r e m lam 0 = lam ↔
      ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j)) := by
  constructor
  · exact fun h => (coefficientWeightPath_constant_of_closed e m lam h).2
  · exact p.coefficientWeightPath_zero_of_pairings r e m lam

/-- A closed coefficient path can only occur at a dominant weight. -/
theorem isDominantWeight_of_coefficientWeightPath_closed (m : Fin r → ℕ)
    (lam : characterLattice p.torus)
    (hclose : p.coefficientWeightPath r e m lam 0 = lam) :
    p.IsDominantWeight lam := by
  intro a
  have h := (coefficientWeightPath_closed_iff e m lam).mp hclose (e.symm a)
  rw [e.apply_symm_apply] at h
  rw [← h]
  exact Int.natCast_nonneg _

variable (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- An ordered coefficient matrix built from the actual root coefficients
and actual rational representative matrices. -/
def steinbergCoefficientMatrix (a : Fin r → p.base.support) (m : Fin r → ℕ) :
    Matrix n n k :=
  (List.ofFn fun j =>
    coefficientMatrix (ρ.restrict (x (a j)).hom) (m j) *
      (ρ.rationalMatrix (s (a j)).point : Matrix n n k)).prod

/-- Every actual coefficient factor sends a weight to its reflected and raised weight. -/
theorem coefficientMatrix_mul_normalizer_mem_weightSpace (a : p.base.support)
    (m : ℕ) {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam) :
    (coefficientMatrix (ρ.restrict (x a).hom) m *
      (ρ.rationalMatrix (s a).point : Matrix n n k)) *ᵥ v ∈
        p.representationWeightSpace ρ (p.coefficientWeightStep a m lam) := by
  have h := (x a).dividedPower_mem_representationWeightSpace ρ m
    ((s a).rationalMatrix_mem_representationWeightSpace ρ lam hv)
  simpa only [coefficientWeightStep, dividedPower_eq_toLin,
    Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

/-- The ordered actual coefficient matrix follows the suffix weight path. -/
theorem steinbergCoefficientMatrix_mem_weightSpace (a : Fin r → p.base.support)
    (m : Fin r → ℕ) {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam) :
    steinbergCoefficientMatrix x s ρ a m *ᵥ v ∈
      p.representationWeightSpace ρ (p.coefficientWeightPath r a m lam 0) := by
  induction r with
  | zero => simpa only [steinbergCoefficientMatrix, List.ofFn_zero, List.prod_nil,
      Matrix.one_mulVec, coefficientWeightPath] using hv
  | succ r ih =>
    have ht := ih (fun j => a j.succ) (fun j => m j.succ)
    have h := coefficientMatrix_mul_normalizer_mem_weightSpace x s ρ (a 0) (m 0) ht
    simpa only [steinbergCoefficientMatrix, List.ofFn_succ, List.prod_cons,
      Matrix.mulVec_mulVec, coefficientWeightPath, Fin.cons_zero] using h

variable (p)

/-- The existing universal character projector, indexed by the actual weight lattice. -/
def representationWeightProjector (lam : characterLattice p.torus) :
    (n → k) →ₗ[k] (n → k) :=
  letI := p.isSplitTorus.isAffineHom
  (ρ.restrict p.inclusion).characterProjector
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)

variable {p}

/-- Only the simple-coroot exponent tuple survives projection back onto the
original weight space after an ordered actual coefficient product. -/
theorem representationWeightProjector_steinbergCoefficient (m : Fin r → ℕ)
    {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam) :
    p.representationWeightProjector ρ lam (steinbergCoefficientMatrix x s ρ e m *ᵥ v) =
      if ∀ j, (m j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j))
      then steinbergCoefficientMatrix x s ρ e m *ᵥ v else 0 := by
  classical
  let := p.isSplitTorus.isAffineHom
  have hmem := steinbergCoefficientMatrix_mem_weightSpace x s ρ e m hv
  have h := (ρ.restrict p.inclusion).characterProjector_of_mem
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)
    ((rationalCharacters.equivCharacterLattice p.torus).symm
      (p.coefficientWeightPath r e m lam 0)) hmem
  change p.representationWeightProjector ρ lam
      (steinbergCoefficientMatrix x s ρ e m *ᵥ v) = _ at h
  simpa only [EquivLike.apply_eq_iff_eq, coefficientWeightPath_closed_iff] using h

/-- Projection back to a nondominant weight annihilates every ordered
coefficient product. -/
theorem representationWeightProjector_steinbergCoefficient_eq_zero_of_not_dominant
    (m : Fin r → ℕ) {lam : characterLattice p.torus} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ lam)
    (hlam : ¬p.IsDominantWeight lam) :
    p.representationWeightProjector ρ lam (steinbergCoefficientMatrix x s ρ e m *ᵥ v) =
      0 := by
  classical
  rw [representationWeightProjector_steinbergCoefficient e x s ρ m hv]
  split_ifs with hm
  · exact False.elim (hlam (isDominantWeight_of_coefficientWeightPath_closed e m lam
      ((coefficientWeightPath_closed_iff e m lam).mpr hm)))
  · rfl

end Langlands.GroupScheme.SplitPinning
