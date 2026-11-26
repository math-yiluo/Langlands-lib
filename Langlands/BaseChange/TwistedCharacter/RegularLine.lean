import Langlands.BaseChange.CyclicNormLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Cofinitely many regular points on a matrix line -/

noncomputable section

namespace Langlands.BaseChange

open Filter JacquetLanglands Matrix _root_.Polynomial

universe u v

section Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {I : Type*}

/-- The polynomial matrix for the affine line from `A` to `B`. -/
def matrixLinePolynomial (A B : Matrix I I R) : Matrix I I R[X] :=
  A.map (C : R →+* R[X]) + (X : R[X]) • (B - A).map (C : R →+* R[X])

@[simp]
theorem matrixLinePolynomial_eval (A B : Matrix I I R) (t : R) :
    (matrixLinePolynomial A B).map (evalRingHom t) = A + t • (B - A) := by
  ext i j
  simp [matrixLinePolynomial, Matrix.smul_apply, smul_eq_mul]

variable [Fintype I] [DecidableEq I]

private def matrixResultant (A : Matrix I I R) : R :=
  A.charpoly.resultant A.charpoly.derivative (Fintype.card I) (Fintype.card I - 1)

private theorem matrixResultant_map (f : R →+* S) (A : Matrix I I R) :
    matrixResultant (A.map f) = f (matrixResultant A) := by
  unfold matrixResultant
  rw [show (A.map f).charpoly = A.charpoly.map f from Matrix.charpoly_map A f,
    derivative_map, resultant_map_map]

end Polynomial

section Cyclic

variable {F : Type u} [Field F]
  {E : Type v} [CommRing E] [Algebra F E] {n l : ℕ} (σ : E ≃ₐ[F] E)

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

private theorem matrixResultant_ne_zero_iff (γ : GeneralLinear n F) :
    matrixResultant γ.val ≠ 0 ↔ IsRegularSemisimple γ := by
  let p := γ.val.charpoly
  have hp : p.Monic := Matrix.charpoly_monic _
  have hdeg : p.natDegree = n := by simp [p, Matrix.charpoly_natDegree_eq_dim]
  have hd : p.derivative.natDegree ≤ n - 1 := hdeg ▸ natDegree_derivative_le p
  unfold matrixResultant
  rw [Fintype.card_fin]
  change p.resultant p.derivative n (n - 1) ≠ 0 ↔ p.Separable
  have hr : p.resultant p.derivative n (n - 1) = p.resultant p.derivative := calc
    _ = p.resultant p.derivative n (p.derivative.natDegree +
        (n - 1 - p.derivative.natDegree)) := by rw [Nat.add_sub_of_le hd]
    _ = _ := by
      rw [resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdeg, coeff_natDegree,
        hp.leadingCoeff, one_pow, one_mul]
  rw [hr, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hp, separable_def]

private theorem matrixResultant_associated {δ : G} {γ : GeneralLinear n F}
    (h : IsNormAssociated σ l δ γ) :
    matrixResultant (cyclicNorm σ l δ).val = algebraMap F E (matrixResultant γ.val) := by
  obtain ⟨x, hx⟩ := h
  have hconj := congrArg (fun g : G => g.val.charpoly) hx
  have hp : (cyclicNorm σ l δ).val.charpoly = γ.val.charpoly.map (algebraMap F E) := by
    simpa only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] using
      hconj.trans (Matrix.charpoly_map γ.val (algebraMap F E))
  unfold matrixResultant
  rw [hp, derivative_map, resultant_map_map]

private def normLinePolynomial (l : ℕ) (A B : Mat) : Matrix (Fin n) (Fin n) E[X] :=
  ((List.range l).map fun k =>
    matrixLinePolynomial ((σ ^ k).mapMatrix A) ((σ ^ k).mapMatrix B)).prod

private theorem normLinePolynomial_eval (A B : Mat) (t : F) (g : G)
    (hg : g.val = A + t • (B - A)) :
    (normLinePolynomial σ l A B).map (evalRingHom (algebraMap F E t)) =
      (cyclicNorm σ l g).val := by
  induction l with
  | zero => simp [normLinePolynomial]
  | succ l ih =>
    have hd : normLinePolynomial σ (l + 1) A B = normLinePolynomial σ l A B *
        matrixLinePolynomial ((σ ^ l).mapMatrix A) ((σ ^ l).mapMatrix B) := by
      simp [normLinePolynomial, List.range_succ]
    rw [hd, ← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, ih, cyclicNorm_succ, Units.val_mul, matrixLinePolynomial_eval]
    congr 1
    change (σ ^ l).mapMatrix A + algebraMap F E t •
        ((σ ^ l).mapMatrix B - (σ ^ l).mapMatrix A) = (σ ^ l).mapMatrix g.val
    rw [hg, map_add, map_smul, map_sub]
    rw [IsScalarTower.algebraMap_smul E]

private theorem eventually_unit_on_matrixLine (g₀ g₁ : G) [Module.Finite F E] :
    ∀ᶠ t : F in cofinite, IsUnit (g₀.val + t • (g₁.val - g₀.val)) := by
  let b := Module.finBasis F Mat
  let e := LinearMap.toMatrixAlgEquiv b
  let L := (e.toAlgHom.comp (Algebra.lmul F Mat)).toLinearMap
  let p := (matrixLinePolynomial (L g₀.val) (L g₁.val)).det
  have hp (t : F) : p.eval t = (L (g₀.val + t • (g₁.val - g₀.val))).det := by
    change evalRingHom t (matrixLinePolynomial (L g₀.val) (L g₁.val)).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply, matrixLinePolynomial_eval, map_add, map_smul, map_sub]
  have h0 : p.eval 0 ≠ 0 := by
    rw [hp]
    simp only [zero_smul, add_zero]
    exact isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1
      (g₀.isUnit.map (e.toAlgHom.comp (Algebra.lmul F Mat))))
  have hp₀ : p ≠ 0 := fun h => h0 (by rw [h, eval_zero])
  filter_upwards [eventually_eval_ne_zero_cofinite hp₀] with t ht
  rw [hp] at ht
  exact (Algebra.lmul_isUnit_iff (R := F)).1
    ((isUnit_map_iff e _).1 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ht)))

/-- Except at finitely many scalar parameters, the matrix line from any invertible
matrix to a σ-regular one consists of invertible σ-regular matrices. -/
theorem eventually_sigmaRegular_on_matrixLine (hE : IsCyclicAlgebra σ l)
    (g₀ g₁ : G) (h₁ : IsSigmaRegular σ l g₁) :
    ∀ᶠ t : F in cofinite, ∃ g : G, g.val = g₀.val + t • (g₁.val - g₀.val) ∧
      IsSigmaRegular σ l g := by
  let _ : Module.Finite F E := hE.1
  let _ : Nontrivial E := Module.finrank_pos_iff.mp (hE.2.1.symm ▸ hE.pos)
  let m : MaximalSpectrum E := Classical.choice inferInstance
  let _ : m.asIdeal.IsMaximal := m.isMaximal
  let K := E ⧸ m.asIdeal
  let q : E →ₐ[F] K := Ideal.Quotient.mkₐ F m.asIdeal
  let R := matrixResultant (normLinePolynomial σ l g₀.val g₁.val)
  let p := R.map q.toRingHom
  have hp (t : F) (g : G) (hg : g.val = g₀.val + t • (g₁.val - g₀.val)) :
      p.eval (algebraMap F K t) = q (matrixResultant (cyclicNorm σ l g).val) := by
    have hr : R.eval (algebraMap F E t) = matrixResultant (cyclicNorm σ l g).val := by
      change evalRingHom (algebraMap F E t) (matrixResultant _) = _
      rw [← matrixResultant_map, normLinePolynomial_eval σ g₀.val g₁.val t g hg]
    rw [show p.eval (algebraMap F K t) = q (R.eval (algebraMap F E t)) by
      rw [← q.commutes t]
      exact eval_map_apply q.toRingHom (algebraMap F E t), hr]
  have hp₀ : p ≠ 0 := by
    intro hpzero
    obtain ⟨γ, hγ, hreg⟩ := h₁
    have ht := hp 1 g₁ (by simp)
    rw [hpzero, eval_zero, matrixResultant_associated σ hγ, q.commutes] at ht
    exact (matrixResultant_ne_zero_iff γ).2 hreg ((algebraMap F K).injective (by simpa using ht.symm))
  have havoid : ∀ᶠ t : F in cofinite, p.eval (algebraMap F K t) ≠ 0 :=
    ((algebraMap F K).injective.tendsto_cofinite).eventually (eventually_eval_ne_zero_cofinite hp₀)
  filter_upwards [eventually_unit_on_matrixLine (F := F) g₀ g₁, havoid] with t hu ht
  let g : G := hu.unit
  have hg : g.val = g₀.val + t • (g₁.val - g₀.val) := hu.unit_spec
  obtain ⟨γ, hγ⟩ := (cyclicNormLemma F E σ l n hE).1 g
  rw [hp t g hg, matrixResultant_associated σ hγ, q.commutes] at ht
  exact ⟨g, hg, γ, hγ, (matrixResultant_ne_zero_iff γ).1 (fun hz => ht (by simp [hz]))⟩

private theorem cyclicNorm_baseChange_eq (g : GeneralLinear n F) :
    cyclicNorm σ l (baseChange F E n g) = baseChange F E n (g ^ l) := by
  induction l with
  | zero => simp
  | succ l ih => rw [cyclicNorm_succ, ih, entrywiseAut_baseChange, pow_succ, map_mul]

/-- Every rank has a σ-regular element over the base itself. -/
theorem exists_sigmaRegular_of_cyclic [CharZero F] (hE : IsCyclicAlgebra σ l) :
    ∃ g : G, IsSigmaRegular σ l g := by
  let a (i : Fin n) : F := ((i.val + 1 : ℕ) : F)
  have ha (i : Fin n) : a i ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)
  have hu : IsUnit (Matrix.diagonal a) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
  let g : GeneralLinear n F := hu.unit
  have hg : g.val = Matrix.diagonal a := hu.unit_spec
  refine ⟨baseChange F E n g, g ^ l, ⟨1, by simp [cyclicNorm_baseChange_eq σ]⟩, ?_⟩
  change (g.val ^ l).charpoly.Separable
  rw [hg, Matrix.diagonal_pow, Matrix.charpoly_diagonal]
  apply separable_prod_X_sub_C_iff.2
  intro i j h
  change a i ^ l = a j ^ l at h
  apply Fin.ext
  have hnat : (i.val + 1) ^ l = (j.val + 1) ^ l := Nat.cast_injective (R := F)
    (by simpa only [Nat.cast_pow, a] using h)
  have hpow : StrictMono (fun a : ℕ => a ^ l) := fun _ _ hlt => Nat.pow_lt_pow_left hlt hE.pos.ne'
  exact Nat.succ_injective (hpow.injective hnat)

end Cyclic

end Langlands.BaseChange
