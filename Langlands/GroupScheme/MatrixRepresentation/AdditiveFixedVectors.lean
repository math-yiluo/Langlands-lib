import Langlands.GroupScheme.MatrixRepresentation.AdditiveRestrictedOperators
import Langlands.Representation.Exponents.DualEigenfunctionalExistence

/-! # Fixed vectors of actual additive-group representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveFixedVectors

open AdditiveDividedPowers AdditiveRestrictedOperators VectorGroupPolynomial

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- The orbit of a vector at the universal polynomial point. -/
def polynomialOrbit (v : n → k) : n → k[X] :=
  univariateMatrix ρ *ᵥ fun i => Polynomial.C (v i)

/-- The subspace annihilated by all positive-degree coefficient operators. -/
def fixedSubmodule : Submodule k (n → k) :=
  ⨅ m : ℕ, ⨅ (_ : 0 < m), LinearMap.ker (dividedPower ρ m)

@[simp] theorem mem_fixedSubmodule (v : n → k) :
    v ∈ fixedSubmodule ρ ↔ ∀ m : ℕ, 0 < m → dividedPower ρ m v = 0 := by
  simp only [fixedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The polynomial orbit has exactly the actual coefficient operators as coefficients. -/
theorem polynomialOrbit_coeff (v : n → k) (i : n) (m : ℕ) :
    (polynomialOrbit ρ v i).coeff m = dividedPower ρ m v i := by
  rw [dividedPower_eq_toLin]
  simp only [polynomialOrbit, Matrix.mulVec, dotProduct, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C]
  rfl

/-- Positive coefficients vanish exactly when the universal orbit is constant. -/
theorem mem_fixedSubmodule_iff_polynomialOrbit (v : n → k) :
    v ∈ fixedSubmodule ρ ↔ polynomialOrbit ρ v = fun i => Polynomial.C (v i) := by
  rw [mem_fixedSubmodule]
  constructor
  · intro h
    funext i
    apply Polynomial.ext
    intro m
    rw [polynomialOrbit_coeff]
    by_cases hm : m = 0
    · subst m
      simp
    · rw [h m (Nat.pos_of_ne_zero hm)]
      simp [Polynomial.coeff_C, hm]
  · intro h m hm
    ext i
    have hi := congrArg (fun w : n → k[X] => (w i).coeff m) h
    rw [polynomialOrbit_coeff] at hi
    simpa [Polynomial.coeff_C, Nat.ne_of_gt hm] using hi

/-- A coefficient-fixed vector remains fixed over every commutative test algebra. -/
theorem affineAction_eq_of_mem_fixedSubmodule {v : n → k} (hv : v ∈ fixedSubmodule ρ)
    (S : CommAlgCat.{u} k)
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
    ρ.affineAction S x (fun i => algebraMap k S (v i)) =
      fun i => algebraMap k S (v i) := by
  obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective
    (R := CommRingCat.of k) (d := 1) S x
  have ht : t = fun _ : Fin 1 => t 0 := funext fun i =>
    congrArg t (Subsingleton.elim i 0)
  rw [ht, affineAction_apply, ← univariateMatrix_aeval]
  have hpoly := (mem_fixedSubmodule_iff_polynomialOrbit ρ v).mp hv
  calc
    _ = fun i => Polynomial.aeval (t 0) (polynomialOrbit ρ v i) := by
      funext i
      simp only [polynomialOrbit, Matrix.mulVec, dotProduct, map_sum, map_mul,
        Matrix.map_apply, Polynomial.aeval_C]
    _ = _ := by
      rw [hpoly]
      simp only [Polynomial.aeval_C]

/-- The coefficient definition detects fixed vectors on all affine test algebras,
without an infinite-field or reducedness assumption. -/
theorem mem_fixedSubmodule_iff_affineAction (v : n → k) :
    v ∈ fixedSubmodule ρ ↔
      ∀ (S : CommAlgCat.{u} k)
        (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
          (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        ρ.affineAction S x (fun i => algebraMap k S (v i)) =
          fun i => algebraMap k S (v i) := by
  constructor
  · exact affineAction_eq_of_mem_fixedSubmodule ρ
  · intro h
    apply (mem_fixedSubmodule_iff_polynomialOrbit ρ v).mpr
    have hX := h (CommAlgCat.of k k[X])
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k[X]) (fun _ => Polynomial.X))
    rw [affineAction_apply,
      ← univariateMatrix_aeval ρ (CommAlgCat.of k k[X]) (Polynomial.X : k[X])] at hX
    have hM : (univariateMatrix ρ).map (Polynomial.aeval (Polynomial.X : k[X])) =
        univariateMatrix ρ := by
      apply Matrix.ext
      intro i j
      exact Polynomial.aeval_X_left_apply (univariateMatrix ρ i j)
    rw [hM] at hX
    exact hX

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The p-power coefficient kernels detect vanishing of every positive coefficient. -/
theorem mem_fixedSubmodule_iff_pPowerOperator (v : n → k) :
    v ∈ fixedSubmodule ρ ↔ ∀ r, pPowerOperator ρ p r v = 0 := by
  rw [mem_fixedSubmodule]
  constructor
  · intro h r
    exact h (p ^ r) (pow_pos (Fact.out : p.Prime).pos _)
  · intro h m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hp : ∃ r, m = p ^ r
      · obtain ⟨r, rfl⟩ := hp
        exact h r
      have hc : ∃ a ∈ Finset.Icc 1 (m - 1), (Nat.choose m a : k) ≠ 0 := by
        by_contra! hc
        apply hp
        refine ⟨multiplicity p m, ?_⟩
        apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hm
        intro a ha
        exact (CharP.cast_eq_iff_mod_eq k p).mp (by simpa using hc a ha)
      obtain ⟨a, ha, hc⟩ := hc
      have ha' := Finset.mem_Icc.mp ha
      have ham : a < m := by omega
      have hma : m - a < m := by omega
      have hmapos : 0 < m - a := Nat.sub_pos_of_lt ham
      have hsum : a + (m - a) = m := Nat.add_sub_of_le ham.le
      have hprod : (dividedPower ρ a * dividedPower ρ (m - a)) v = 0 := by
        rw [Module.End.mul_apply, ih (m - a) hma hmapos, map_zero]
      rw [dividedPower_mul, hsum, LinearMap.smul_apply] at hprod
      exact (smul_eq_zero.mp hprod).resolve_left hc

/-- The actual fixed subspace is the intersection of the p-power coefficient kernels. -/
theorem fixedSubmodule_eq_iInf_ker_pPowerOperator :
    fixedSubmodule ρ = ⨅ r, LinearMap.ker (pPowerOperator ρ p r) := by
  ext v
  simp only [mem_fixedSubmodule_iff_pPowerOperator ρ p, Submodule.mem_iInf, LinearMap.mem_ker]

include p in
/-- A nonzero finite-dimensional additive-group representation has a nonzero fixed vector. -/
theorem exists_nonzero_mem_fixedSubmodule [Nonempty n] :
    ∃ v : n → k, v ≠ 0 ∧ v ∈ fixedSubmodule ρ := by
  obtain ⟨v, hv, h⟩ := Langlands.DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero
    (pPowerOperator ρ p)
    (fun r s => pPowerOperator_commute ρ p r s)
    (fun r => ⟨p, pPowerOperator_pow_char ρ p r⟩)
  exact ⟨v, hv, (mem_fixedSubmodule_iff_pPowerOperator ρ p v).mpr h⟩

include p in
/-- The nonzero fixed vector is fixed after scalar extension to every affine test algebra. -/
theorem exists_fixed_vector [Nonempty n] :
    ∃ v : n → k, v ≠ 0 ∧
      ∀ (S : CommAlgCat.{u} k)
        (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
          (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        ρ.affineAction S x (fun i => algebraMap k S (v i)) =
          fun i => algebraMap k S (v i) := by
  obtain ⟨v, hv, h⟩ := exists_nonzero_mem_fixedSubmodule ρ p
  exact ⟨v, hv, (mem_fixedSubmodule_iff_affineAction ρ v).mp h⟩

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Restriction identifies coefficient-fixed vectors with vectors fixed along the
supplied additive-group morphism over every commutative test algebra. -/
theorem mem_fixedSubmodule_restrict_iff_affineAction
    (σ : MatrixRepresentation G n)
    (f : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) (v : n → k) :
    v ∈ fixedSubmodule (σ.restrict f) ↔
      ∀ (S : CommAlgCat.{u} k)
        (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
          (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        σ.affineAction S (x ≫ f.hom.hom) (fun i => algebraMap k S (v i)) =
          fun i => algebraMap k S (v i) := by
  rw [mem_fixedSubmodule_iff_affineAction]
  constructor
  · intro h S x
    rw [← affineAction_restrict σ f S x]
    exact h S x
  · intro h S x
    rw [affineAction_restrict σ f S x]
    exact h S x

include p in
/-- A supplied additive-group morphism fixes a nonzero vector in any nonzero
finite-dimensional matrix representation, over all commutative test algebras. -/
theorem exists_fixed_vector_restrict [Nonempty n]
    (σ : MatrixRepresentation G n)
    (f : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) :
    ∃ v : n → k, v ≠ 0 ∧
      ∀ (S : CommAlgCat.{u} k)
        (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
          (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        σ.affineAction S (x ≫ f.hom.hom) (fun i => algebraMap k S (v i)) =
          fun i => algebraMap k S (v i) := by
  obtain ⟨v, hv, h⟩ := exists_nonzero_mem_fixedSubmodule (σ.restrict f) p
  exact ⟨v, hv, (mem_fixedSubmodule_restrict_iff_affineAction σ f v).mp h⟩

end Langlands.GroupScheme.MatrixRepresentation.AdditiveFixedVectors
