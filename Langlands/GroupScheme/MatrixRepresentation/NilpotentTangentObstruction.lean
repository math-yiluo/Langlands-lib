import Langlands.GroupScheme.MatrixRepresentation.SymmetricDifferential
import Langlands.GroupScheme.MatrixRepresentation.SymmetricFrobenius
import Langlands.GroupScheme.MatrixRepresentation.Reindex
import Langlands.Algebra.SymmetricFrobeniusObstruction

/-! # No nonzero nilpotent tangent matrices for a linearly reductive group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.SymmetricMatrix

namespace SymmetricDifferential

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- The linear polynomial representing an original coordinate vector. -/
def linearForm : (n → k) →ₗ[k] MvPolynomial n k where
  toFun v := ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i
  map_add' v w := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply]
    rw [Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_assoc _ _ _

omit [DecidableEq n] in
@[simp]
theorem linearForm_apply (v : n → k) :
    linearForm v = ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i := rfl

@[simp]
theorem linearForm_single (j : n) : linearForm (Pi.single j 1 : n → k) =
    MvPolynomial.X j := by
  simp [linearForm, Pi.single_apply, ite_mul]

/-- Coefficients recover the original vector from its linear polynomial. -/
theorem linearForm_coeff (v : n → k) (j : n) :
    (linearForm v).coeff (Finsupp.single j 1) = v j := by
  simp [linearForm, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), eq_comm]

theorem linearForm_injective : Function.Injective (linearForm (k := k) (n := n)) := by
  intro v w h
  funext j
  exact (linearForm_coeff v j).symm.trans
    ((congrArg (fun P : MvPolynomial n k => P.coeff (Finsupp.single j 1)) h).trans
      (linearForm_coeff w j))

/-- The polynomial derivation restricts to the original matrix action on
linear forms. -/
theorem derivation_linearForm (N : Matrix n n k) (v : n → k) :
    derivation N (linearForm v) = linearForm (N *ᵥ v) := by
  have h : (derivation N).toLinearMap.comp linearForm =
      linearForm.comp N.mulVecLin := by
    apply (Pi.basisFun k n).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, linearForm_single,
      Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul]
    change derivation N (MvPolynomial.X j) = linearForm (fun i => N i j)
    rw [derivation_X]
    rfl
  exact LinearMap.congr_fun h v

omit [DecidableEq n] in
theorem linearForm_isHomogeneous (v : n → k) :
    (linearForm v).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ 1
    (fun i _ => (MvPolynomial.isHomogeneous_X k i).C_mul (v i))

omit [DecidableEq n] in
/-- The coordinate vector of a linear form's Frobenius power lies in the
actual pure-power range, without a perfectness assumption. -/
theorem linearForm_pow_coordinates (p : ℕ) [ExpChar k p] (v : n → k) :
    (fun a : Index n p => ((linearForm v) ^ p).coeff a.val) =
      (SymmetricFrobenius.inclusion k p : Matrix (Index n p) n k) *ᵥ
        (fun i => (v i) ^ p) := by
  let F := characteristicPowerMap k p (MvPolynomial n k) 1
  have h := map_sum F (fun i => MvPolynomial.C (v i) * MvPolynomial.X i) Finset.univ
  have hpow : (linearForm v) ^ p =
      ∑ i, MvPolynomial.C ((v i) ^ p) * MvPolynomial.X i ^ p := by
    simpa only [F, characteristicPowerMap_apply, pow_one, mul_pow, ← map_pow,
      linearForm_apply] using h
  funext a
  rw [hpow]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    Matrix.mulVec, dotProduct, SymmetricFrobenius.inclusion, SymmetricFrobenius.powerVector]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- The symmetric differential kills the whole Frobenius range in
characteristic `p`. -/
theorem matrix_mul_inclusion_eq_zero (p : ℕ) [CharP k p] (N : Matrix n n k) :
    matrix N p * (SymmetricFrobenius.inclusion k p : Matrix (Index n p) n k) = 0 := by
  apply Matrix.ext
  intro a j
  let P : MvPolynomial.homogeneousSubmodule n k p :=
    ⟨MvPolynomial.X j ^ p, MvPolynomial.isHomogeneous_X_pow (R := k) j p⟩
  have h := congrFun (matrix_mulVec N p P) a
  change (matrix N p *ᵥ SymmetricFrobenius.powerVector k p j) a =
    (derivation N (MvPolynomial.X j ^ p)).coeff a.val at h
  rw [Langlands.Algebra.SymmetricDerivation.derivation_pow_eq_zero p] at h
  exact h.trans (by simp)

/-- A nonzero nilpotent matrix cannot commute with a projection onto the
Frobenius range of its symmetric differential. -/
theorem not_isProj_of_isNilpotent (p : ℕ) [CharP k p] [ExpChar k p] (hp : 0 < p)
    (N : Matrix n n k) (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (P : Module.End k (Index n p → k))
    (hcomm : LinearMap.toMatrix' P * matrix N p = matrix N p * LinearMap.toMatrix' P) :
    ¬ LinearMap.IsProj (symmetricFrobeniusSubspace k n p) P := by
  intro hP
  let E := (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k))
  let f := E N
  have hf : IsNilpotent f := hN.map E
  have hf0 : f ≠ 0 := by
    intro hf0
    exact hN0 (E.injective (hf0.trans (map_zero E).symm))
  obtain ⟨x, y, hfx, hfy, hy⟩ :=
    Langlands.Algebra.SymmetricDerivation.exists_chain_of_isNilpotent f hf hf0
  change N *ᵥ x = y at hfx
  change N *ᵥ y = 0 at hfy
  have hzw : derivation N ((linearForm y) ^ (p - 1) * linearForm x) =
      (linearForm y) ^ p := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, derivation_linearForm,
      hfx, hfy, map_zero, smul_eq_mul, mul_zero, smul_zero, add_zero]
    rw [← pow_succ, Nat.sub_add_cancel hp]
  let z : MvPolynomial.homogeneousSubmodule n k p :=
    ⟨(linearForm y) ^ (p - 1) * linearForm x, by
      change ((linearForm y) ^ (p - 1) * linearForm x).IsHomogeneous p
      have h := ((linearForm_isHomogeneous y).pow (p - 1)).mul
        (linearForm_isHomogeneous x)
      simpa only [one_mul, Nat.sub_add_cancel hp] using h⟩
  let w : MvPolynomial.homogeneousSubmodule n k p :=
    ⟨(linearForm y) ^ p, by
      change ((linearForm y) ^ p).IsHomogeneous p
      simpa only [one_mul] using (linearForm_isHomogeneous y).pow p⟩
  let zv := (basis k n p).equivFun z
  let wv := (basis k n p).equivFun w
  have hwmem : wv ∈ symmetricFrobeniusSubspace k n p :=
    ⟨fun i => y i ^ p, (linearForm_pow_coordinates p y).symm⟩
  have hw0 : wv ≠ 0 := by
    intro heq
    have hw := (basis k n p).equivFun.injective (heq.trans (map_zero _).symm)
    have hv := congrArg Subtype.val hw
    have hyL : linearForm y ≠ 0 := fun h =>
      hy (linearForm_injective (h.trans (map_zero _).symm))
    exact pow_ne_zero p hyL hv
  have hdzw : matrix N p *ᵥ zv = wv := by
    rw [matrix_mulVec]
    change (fun a : Index n p => (derivation N
      ((linearForm y) ^ (p - 1) * linearForm x)).coeff a.val) = _
    rw [hzw]
    rfl
  have hdzP : matrix N p *ᵥ P zv = 0 := by
    obtain ⟨a, ha⟩ := hP.map_mem zv
    rw [← ha]
    change matrix N p *ᵥ ((SymmetricFrobenius.inclusion k p : Matrix (Index n p) n k) *ᵥ a) = 0
    rw [Matrix.mulVec_mulVec, matrix_mul_inclusion_eq_zero, Matrix.zero_mulVec]
  have hc := congrArg (fun M : Matrix (Index n p) (Index n p) k => M *ᵥ zv) hcomm
  simp only [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hc
  rw [hdzw, hP.map_id wv hwmem, hdzP] at hc
  exact hw0 hc

end SymmetricDifferential

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A representation is Frobenius-splittable when its actual symmetric power
has an all-test equivariant projection onto the pure-power span. -/
def IsFrobeniusSplittable (ρ : MatrixRepresentation G n) (p : ℕ) : Prop :=
  ∃ P : Module.End k (Index n p → k),
    (ρ.symmetricPower p).IsEquivariantProjection (symmetricFrobeniusSubspace k n p) P

/-- Frobenius splittability restricts along every group-scheme morphism. -/
theorem IsFrobeniusSplittable.restrict {H : GroupScheme (Spec (CommRingCat.of k))}
    {ρ : MatrixRepresentation G n} {p : ℕ} (hs : ρ.IsFrobeniusSplittable p)
    (f : H ⟶ G) : (ρ.restrict f).IsFrobeniusSplittable p := by
  obtain ⟨P, hP⟩ := hs
  refine ⟨P, ?_⟩
  rw [symmetricPower_restrict]
  exact hP.restrict f

/-- The unchanged finite-coordinate linear-reductivity premise supplies an
actual Frobenius splitting for every representation. -/
theorem isFrobeniusSplittable_of_linearlyReductive (p : ℕ) [ExpChar k p]
    (hLR : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G n) : ρ.IsFrobeniusSplittable p :=
  exists_equivariantProjection_symmetricFrobeniusSubspace ρ p
    (isSemisimple_of_fin_linearlyReductive hLR _)

/-- In positive characteristic, a Frobenius-splittable representation has no
nonzero nilpotent tangent matrix. -/
theorem tangentMatrix_eq_zero_of_isNilpotent_of_isFrobeniusSplittable
    (p : ℕ) [CharP k p] (hp : p ≠ 0) (ρ : MatrixRepresentation G n)
    (hs : ρ.IsFrobeniusSplittable p) (X : lieKernel G k)
    (hN : IsNilpotent (ρ.tangentMatrix k X)) : ρ.tangentMatrix k X = 0 := by
  let : ExpChar k p := ExpChar.prime ((CharP.char_is_prime_or_zero k p).resolve_right hp)
  by_contra hN0
  obtain ⟨P, hP⟩ := hs
  have hc := hP.1.tangentMatrix X
  rw [symmetricPower_tangentMatrix] at hc
  exact SymmetricDifferential.not_isProj_of_isNilpotent p (Nat.pos_of_ne_zero hp)
    (ρ.tangentMatrix k X) hN hN0 P hc hP.2

/-- Any nilpotent tangent matrix of any finite representation of a linearly
reductive group in positive characteristic is zero. -/
theorem tangentMatrix_eq_zero_of_isNilpotent_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hLR : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G n) (X : lieKernel G k)
    (hN : IsNilpotent (ρ.tangentMatrix k X)) : ρ.tangentMatrix k X = 0 := by
  let : ExpChar k p := ExpChar.prime ((CharP.char_is_prime_or_zero k p).resolve_right hp)
  exact tangentMatrix_eq_zero_of_isNilpotent_of_isFrobeniusSplittable p hp ρ
    (isFrobeniusSplittable_of_linearlyReductive p hLR ρ) X hN

end Langlands.GroupScheme.MatrixRepresentation
