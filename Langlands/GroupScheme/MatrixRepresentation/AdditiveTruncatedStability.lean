import Langlands.GroupScheme.MatrixRepresentation.AdditiveInvariantSubspaces
import Mathlib.RingTheory.AdjoinRoot

/-! # Finite-height stability for actual additive-group representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveTruncatedStability

open AdditiveDividedPowers AdditiveRestrictedOperators AdditiveFixedVectors
  AdditiveInvariantSubspaces

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- Stability at every scalar with vanishing N-th power, over every test algebra. -/
def IsStableAtNilpotentScalars (N : ℕ) (W : Submodule k (n → k)) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : A), t ^ N = 0 →
    ∀ v ∈ W, ∀ ℓ : A →ₗ[k] k,
      (fun i => ℓ (ρ.affineAction A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t))
        (fun j => algebraMap k A (v j)) i)) ∈ W

/-- Coefficient extraction in the universal algebra with an N-nilpotent scalar. -/
def truncatedCoeff (N m : ℕ) : AdjoinRoot (Polynomial.X ^ N : k[X]) →ₗ[k] k :=
  (Polynomial.lcoeff k m).comp
    (AdjoinRoot.modByMonicHom ((Polynomial.monic_X (R := k)).pow N))

/-- The universal scalar has vanishing N-th power, including the case N = 0. -/
theorem root_pow (N : ℕ) :
    AdjoinRoot.root (Polynomial.X ^ N : k[X]) ^ N = 0 := by
  simpa only [map_pow, AdjoinRoot.mk_X] using
    (AdjoinRoot.mk_self (f := (Polynomial.X ^ N : k[X])))

/-- In degrees below N, the universal nilpotent test recovers the original
polynomial coefficient. -/
theorem truncatedCoeff_aeval (N m : ℕ) (hm : m < N) (f : k[X]) :
    truncatedCoeff (k := k) N m
      (Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ N : k[X])) f) =
        f.coeff m := by
  simp only [truncatedCoeff, LinearMap.comp_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.modByMonicHom_mk, Polynomial.lcoeff_apply]
  have h := congrArg (fun q : k[X] => q.coeff m)
    (Polynomial.modByMonic_add_div f (Polynomial.X ^ N))
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    ite_eq_right (Nat.not_le.mpr hm), add_zero] using h

/-- Nilpotent scalar tests detect exactly the coefficient operators below N.
No characteristic or infinitude assumption is needed. -/
theorem isStableAtNilpotentScalars_iff_invariant_dividedPower
    (N : ℕ) (W : Submodule k (n → k)) :
    IsStableAtNilpotentScalars ρ N W ↔
      ∀ m < N, ∀ v ∈ W, dividedPower ρ m v ∈ W := by
  constructor
  · intro h m hm v hv
    have hX := h (CommAlgCat.of k (AdjoinRoot (Polynomial.X ^ N : k[X])))
      (AdjoinRoot.root (Polynomial.X ^ N : k[X])) (root_pow N)
      v hv (truncatedCoeff N m)
    change (fun i => truncatedCoeff N m
      (ρ.affineAction (CommAlgCat.of k (AdjoinRoot (Polynomial.X ^ N : k[X])))
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
          (CommAlgCat.of k (AdjoinRoot (Polynomial.X ^ N : k[X])))
          (fun _ => AdjoinRoot.root (Polynomial.X ^ N : k[X])))
        (fun j => algebraMap k (AdjoinRoot (Polynomial.X ^ N : k[X])) (v j)) i)) ∈ W
      at hX
    rw [affineAction_eq_aeval_polynomialOrbit] at hX
    simpa only [truncatedCoeff_aeval N m hm, polynomialOrbit_coeff] using hX
  · intro h A t ht v hv ℓ
    obtain ⟨M, hM⟩ := linearFunctional_affineAction_eq_sum ρ v
    rw [hM]
    apply W.sum_mem
    intro m _
    by_cases hm : m < N
    · exact W.smul_mem _ (h m hm v hv)
    · have htm : t ^ m = 0 := pow_eq_zero_of_le (Nat.le_of_not_gt hm) ht
      simpa only [htm, map_zero, zero_smul] using W.zero_mem

/-- Ordinary all-test stability implies stability at every nilpotence bound. -/
theorem isStableAtNilpotentScalars_of_isStableSubspace
    (W : Submodule k (n → k)) (hW : IsStableSubspace ρ W) (N : ℕ) :
    IsStableAtNilpotentScalars ρ N W := by
  intro A t _ v hv ℓ
  exact hW A
    (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t)) v hv ℓ

/-- Increasing the nilpotence bound strengthens stability. -/
theorem IsStableAtNilpotentScalars.mono
    {N M : ℕ} {W : Submodule k (n → k)}
    (h : IsStableAtNilpotentScalars ρ M W) (hNM : N ≤ M) :
    IsStableAtNilpotentScalars ρ N W := by
  intro A t ht
  exact h A t (pow_eq_zero_of_le hNM ht)

/-- Fixedness at every scalar with vanishing N-th power over every test algebra. -/
def IsFixedAtNilpotentScalars (N : ℕ) (v : n → k) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : A), t ^ N = 0 →
    ρ.affineAction A
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t))
      (fun j => algebraMap k A (v j)) =
        fun j => algebraMap k A (v j)

/-- The subspace killed by all positive coefficient operators of degree below N. -/
def truncatedFixedSubmodule (N : ℕ) : Submodule k (n → k) :=
  ⨅ m : ℕ, ⨅ (_ : 0 < m), ⨅ (_ : m < N), LinearMap.ker (dividedPower ρ m)

@[simp] theorem mem_truncatedFixedSubmodule (N : ℕ) (v : n → k) :
    v ∈ truncatedFixedSubmodule ρ N ↔
      ∀ m : ℕ, 0 < m → m < N → dividedPower ρ m v = 0 := by
  simp only [truncatedFixedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The bounded coefficient kernel identifies actual fixed vectors at every
N-nilpotent scalar, over arbitrary test algebras. -/
theorem mem_truncatedFixedSubmodule_iff_isFixedAtNilpotentScalars
    (N : ℕ) (v : n → k) :
    v ∈ truncatedFixedSubmodule ρ N ↔ IsFixedAtNilpotentScalars ρ N v := by
  rw [mem_truncatedFixedSubmodule]
  constructor
  · intro h A t ht
    rw [affineAction_eq_aeval_polynomialOrbit]
    funext i
    have hdvd : (Polynomial.X ^ N : k[X]) ∣
        polynomialOrbit ρ v i - Polynomial.C (v i) := by
      apply Polynomial.X_pow_dvd_iff.mpr
      intro m hm
      rw [Polynomial.coeff_sub, polynomialOrbit_coeff]
      by_cases hm0 : m = 0
      · subst m
        simp
      · rw [h m (Nat.pos_of_ne_zero hm0) hm]
        simp [Polynomial.coeff_C, hm0]
    have heval := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero (x := t) hdvd
      (by simpa only [map_pow, Polynomial.aeval_X] using ht)
    simpa only [map_sub, Polynomial.aeval_C, sub_eq_zero] using heval
  · intro h m hmpos hm
    have hX := h (CommAlgCat.of k (AdjoinRoot (Polynomial.X ^ N : k[X])))
      (AdjoinRoot.root (Polynomial.X ^ N : k[X])) (root_pow N)
    rw [affineAction_eq_aeval_polynomialOrbit] at hX
    funext i
    have hi := congrArg (fun w : n → AdjoinRoot (Polynomial.X ^ N : k[X]) =>
      truncatedCoeff N m (w i)) hX
    have hC := truncatedCoeff_aeval (k := k) N m hm (Polynomial.C (v i))
    rw [Polynomial.aeval_C] at hC
    simpa only [truncatedCoeff_aeval N m hm, polynomialOrbit_coeff, hC,
      Polynomial.coeff_C, ite_eq_right (Nat.ne_of_gt hmpos), Pi.zero_apply] using hi

/-- Full additive fixedness implies membership in each bounded fixed subspace. -/
theorem fixedSubmodule_le_truncatedFixedSubmodule (N : ℕ) :
    AdditiveFixedVectors.fixedSubmodule ρ ≤ truncatedFixedSubmodule ρ N := by
  intro v hv
  exact (mem_truncatedFixedSubmodule ρ N v).mpr fun m hm _ =>
    (AdditiveFixedVectors.mem_fixedSubmodule ρ v).mp hv m hm

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The p-power operators below height s generate each coefficient of
degree less than p^s. -/
theorem dividedPower_mem_of_pPowerOperator_mem_lt (s : ℕ)
    (A : Subalgebra k (Module.End k (n → k)))
    (hA : ∀ r < s, pPowerOperator ρ p r ∈ A) (m : ℕ) :
    m < p ^ s → dividedPower ρ m ∈ A := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hm0 : m = 0
    · subst m
      rw [dividedPower_zero]
      exact A.one_mem
    by_cases hp : ∃ r, m = p ^ r
    · obtain ⟨r, rfl⟩ := hp
      exact hA r ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hm)
    have hc : ∃ a ∈ Finset.Icc 1 (m - 1), (Nat.choose m a : k) ≠ 0 := by
      by_contra! hc
      apply hp
      refine ⟨multiplicity p m, ?_⟩
      apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (Nat.pos_of_ne_zero hm0)
      intro a ha
      exact (CharP.cast_eq_iff_mod_eq k p).mp (by simpa using hc a ha)
    obtain ⟨a, ha, hc⟩ := hc
    have ha' := Finset.mem_Icc.mp ha
    have ham : a < m := by omega
    have hma : m - a < m := by omega
    have hsum : a + (m - a) = m := Nat.add_sub_of_le ham.le
    have hprod := A.mul_mem (ih a ham (ham.trans hm)) (ih (m - a) hma (hma.trans hm))
    rw [dividedPower_mul, hsum] at hprod
    have hscaled := A.smul_mem hprod ((Nat.choose m a : k)⁻¹)
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscaled

/-- Bounded coefficient invariance is equivalent to invariance under the
first s p-power operators. -/
theorem invariant_dividedPower_lt_iff_invariant_pPowerOperator_lt
    (s : ℕ) (W : Submodule k (n → k)) :
    (∀ m < p ^ s, ∀ v ∈ W, dividedPower ρ m v ∈ W) ↔
      ∀ r < s, ∀ v ∈ W, pPowerOperator ρ p r v ∈ W := by
  constructor
  · intro h r hr
    exact h (p ^ r) ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr hr)
  · intro h
    let A : Subalgebra k (Module.End k (n → k)) :=
      { carrier := {f | ∀ v ∈ W, f v ∈ W}
        algebraMap_mem' := by
          intro c v hv
          exact W.smul_mem c hv
        add_mem' := by
          intro f g hf hg v hv
          exact W.add_mem (hf v hv) (hg v hv)
        mul_mem' := by
          intro f g hf hg v hv
          exact hf _ (hg v hv) }
    intro m hm v hv
    exact dividedPower_mem_of_pPowerOperator_mem_lt ρ p s A h m hm v hv

/-- In prime characteristic, stability at every scalar killed by the p^s-th
power is equivalent to invariance under the first s actual p-power operators. -/
theorem isStableAtNilpotentScalars_iff_invariant_pPowerOperator_lt
    (s : ℕ) (W : Submodule k (n → k)) :
    IsStableAtNilpotentScalars ρ (p ^ s) W ↔
      ∀ r < s, ∀ v ∈ W, pPowerOperator ρ p r v ∈ W := by
  rw [isStableAtNilpotentScalars_iff_invariant_dividedPower,
    invariant_dividedPower_lt_iff_invariant_pPowerOperator_lt]

/-- The bounded coefficient fixed space is the common kernel of the first
s p-power operators. -/
theorem mem_truncatedFixedSubmodule_iff_pPowerOperator_lt (s : ℕ) (v : n → k) :
    v ∈ truncatedFixedSubmodule ρ (p ^ s) ↔
      ∀ r < s, pPowerOperator ρ p r v = 0 := by
  rw [mem_truncatedFixedSubmodule]
  constructor
  · intro h r hr
    exact h (p ^ r) (pow_pos (Fact.out : p.Prime).pos _)
      ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr hr)
  · intro h m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmpos hm
      by_cases hp : ∃ r, m = p ^ r
      · obtain ⟨r, rfl⟩ := hp
        exact h r ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hm)
      have hc : ∃ a ∈ Finset.Icc 1 (m - 1), (Nat.choose m a : k) ≠ 0 := by
        by_contra! hc
        apply hp
        refine ⟨multiplicity p m, ?_⟩
        apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hmpos
        intro a ha
        exact (CharP.cast_eq_iff_mod_eq k p).mp (by simpa using hc a ha)
      obtain ⟨a, ha, hc⟩ := hc
      have ha' := Finset.mem_Icc.mp ha
      have ham : a < m := by omega
      have hma : m - a < m := by omega
      have hmapos : 0 < m - a := Nat.sub_pos_of_lt ham
      have hsum : a + (m - a) = m := Nat.add_sub_of_le ham.le
      have hprod : (dividedPower ρ a * dividedPower ρ (m - a)) v = 0 := by
        rw [Module.End.mul_apply, ih (m - a) hma hmapos (hma.trans hm), map_zero]
      rw [dividedPower_mul, hsum, LinearMap.smul_apply] at hprod
      exact (smul_eq_zero.mp hprod).resolve_left hc

/-- Fixed vectors on all nilpotent tests of height s are the common kernel
of precisely the first s actual p-power operators. -/
theorem isFixedAtNilpotentScalars_iff_pPowerOperator_lt (s : ℕ) (v : n → k) :
    IsFixedAtNilpotentScalars ρ (p ^ s) v ↔
      ∀ r < s, pPowerOperator ρ p r v = 0 := by
  rw [← mem_truncatedFixedSubmodule_iff_isFixedAtNilpotentScalars,
    mem_truncatedFixedSubmodule_iff_pPowerOperator_lt]

/-- Equality of the bounded fixed subspace with the finite operator-kernel
intersection. At height zero this is the whole space. -/
theorem truncatedFixedSubmodule_eq_iInf_ker_pPowerOperator (s : ℕ) :
    truncatedFixedSubmodule ρ (p ^ s) =
      ⨅ r : Fin s, LinearMap.ker (pPowerOperator ρ p r) := by
  ext v
  simp only [mem_truncatedFixedSubmodule_iff_pPowerOperator_lt ρ p,
    Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h r => h r r.isLt, fun h r hr => h ⟨r, hr⟩⟩

/-- Invariance on every finite height detects ordinary all-test stability. -/
theorem isStableSubspace_iff_forall_height (W : Submodule k (n → k)) :
    IsStableSubspace ρ W ↔
      ∀ s : ℕ, IsStableAtNilpotentScalars ρ (p ^ s) W := by
  rw [isStableSubspace_iff_invariant_pPowerOperator ρ p]
  constructor
  · intro h s
    exact (isStableAtNilpotentScalars_iff_invariant_pPowerOperator_lt ρ p s W).mpr
      fun r _ => h r
  · intro h r
    exact (isStableAtNilpotentScalars_iff_invariant_pPowerOperator_lt ρ p (r + 1) W).mp
      (h (r + 1)) r (Nat.lt_succ_self r)

/-- Fixedness at every finite height detects fixedness on every relative
scheme test of the actual additive group. -/
theorem isFixedVector_iff_forall_height (v : n → k) :
    ρ.IsFixedVector v ↔ ∀ s : ℕ, IsFixedAtNilpotentScalars ρ (p ^ s) v := by
  rw [isFixedVector_iff_pPowerOperator ρ p]
  constructor
  · intro h s
    exact (isFixedAtNilpotentScalars_iff_pPowerOperator_lt ρ p s v).mpr fun r _ => h r
  · intro h r
    exact (isFixedAtNilpotentScalars_iff_pPowerOperator_lt ρ p (r + 1) v).mp
      (h (r + 1)) r (Nat.lt_succ_self r)

end Langlands.GroupScheme.MatrixRepresentation.AdditiveTruncatedStability
