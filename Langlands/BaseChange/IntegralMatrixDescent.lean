import Langlands.Algebra.CyclicSemilinearFixedSpan
import Langlands.BaseChange.Norm
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Integral descent for a matrix cocycle with trivial cyclic norm. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix IsLocalRing

universe u v

section InvertibleColumns

variable {S : Type v} [CommRing S] [IsLocalRing S]

private def residueVectors (n : ℕ) : (Fin n → S) →ₛₗ[residue S] (Fin n → ResidueField S) where
  toFun x i := residue S (x i)
  map_add' x y := funext fun i => map_add (residue S) (x i) (y i)
  map_smul' a x := funext fun i => map_mul (residue S) a (x i)

/-- A spanning set of column vectors over a local ring contains the columns of
an invertible matrix. -/
theorem exists_generalLinear_columns_mem {n : ℕ} (X : Set (Fin n → S))
    (hX : Submodule.span S X = ⊤) :
    ∃ g : GeneralLinear n S, ∀ j, (fun i => g i j) ∈ X := by
  classical
  let k := ResidueField S
  let red := residueVectors (S := S) n
  let : RingHomSurjective (residue S) := ⟨residue_surjective⟩
  have hred : Function.Surjective red := by
    intro y
    choose x hx using fun i => residue_surjective (y i)
    exact ⟨x, funext hx⟩
  have hspan : Submodule.span k (red '' X) = ⊤ := by
    rw [← Submodule.map_span, hX, Submodule.map_top, LinearMap.range_eq_top.mpr hred]
  have hdim : Module.finrank k (Submodule.span k (red '' X)) = n := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  have hchoose := Submodule.exists_fun_fin_finrank_span_eq k (red '' X)
  rw [hdim] at hchoose
  obtain ⟨v, hv, _, hlin⟩ := hchoose
  choose w hw hwv using hv
  let A : Matrix (Fin n) (Fin n) S := fun i j => w j i
  have hcols : (A.map (residue S)).col = v := by
    funext j i
    exact congrFun (hwv j) i
  have hdet : IsUnit A.det := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hdetred : ((RingHom.mapMatrix (residue S)) A).det ≠ 0 :=
      Matrix.nonsingular_iff_det_ne_zero.mp
        (Matrix.linearIndependent_col_iff.mp (hcols.symm ▸ hlin))
    simpa only [RingHom.map_det] using hdetred
  exact ⟨Matrix.GeneralLinearGroup.mk'' A hdet, hw⟩

end InvertibleColumns

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The additive operator on column vectors acting by `g` after applying `σ`
coordinatewise. -/
def semilinearVectorOperator (σ : S ≃ₐ[R] S) {n : ℕ} (g : GeneralLinear n S) :
    AddMonoid.End (Fin n → S) where
  toFun x := (g : Matrix (Fin n) (Fin n) S) *ᵥ fun i => σ (x i)
  map_zero' := by
    change (g : Matrix (Fin n) (Fin n) S) *ᵥ (fun _ => σ 0) = 0
    rw [map_zero]
    exact Matrix.mulVec_zero _
  map_add' x y := by
    simp only [Pi.add_apply, map_add, ← Pi.add_def, Matrix.mulVec_add]

@[simp] theorem semilinearVectorOperator_apply (σ : S ≃ₐ[R] S) {n : ℕ}
    (g : GeneralLinear n S) (x : Fin n → S) :
    semilinearVectorOperator σ g x = (g : Matrix (Fin n) (Fin n) S) *ᵥ fun i => σ (x i) := rfl

theorem semilinearVectorOperator_smul (σ : S ≃ₐ[R] S) {n : ℕ}
    (g : GeneralLinear n S) (a : S) (x : Fin n → S) :
    semilinearVectorOperator σ g (a • x) = σ a • semilinearVectorOperator σ g x := by
  rw [semilinearVectorOperator_apply, semilinearVectorOperator_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [smul_eq_mul]

theorem semilinearVectorOperator_pow_apply (σ : S ≃ₐ[R] S) {n : ℕ}
    (g : GeneralLinear n S) (l : ℕ) (x : Fin n → S) :
    (semilinearVectorOperator σ g ^ l) x = (cyclicNorm σ l g : Matrix (Fin n) (Fin n) S) *ᵥ
      fun i => (σ ^ l) (x i) := by
  induction l generalizing x with
  | zero => simp [show (1 : AddMonoid.End (Fin n → S)) x = x from rfl]
  | succ l ih =>
    rw [pow_succ, cyclicNorm_succ]
    change (semilinearVectorOperator σ g ^ l) (semilinearVectorOperator σ g x) = _
    rw [ih]
    simp only [semilinearVectorOperator_apply, GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact RingHom.map_mulVec (σ ^ l).toRingHom (g : Matrix (Fin n) (Fin n) S)
      (fun j => σ (x j)) i

/-- If `0 < l`, `σ ^ l = 1`, and the `l`-factor cyclic norm of `g` is one,
there is an integral matrix that twisted-conjugates `g` to one provided
the conjugates of one scalar indexed by `Fin l` have pairwise unit differences. -/
theorem exists_integral_twistedConj_eq_one [IsLocalRing S] (σ : S ≃ₐ[R] S)
    {n l : ℕ} (hl : 0 < l) (hσ : σ ^ l = 1) (g : GeneralLinear n S)
    (hg : cyclicNorm σ l g = 1) (a : S)
    (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a)) :
    ∃ c : GeneralLinear n S, c⁻¹ * g * entrywiseAut σ n c = 1 := by
  let D := semilinearVectorOperator σ g
  have hD : D ^ l = 1 := by
    apply AddMonoidHom.ext
    intro x
    change (semilinearVectorOperator σ g ^ l) x = x
    rw [semilinearVectorOperator_pow_apply, hg, hσ]
    simp
  have hsep : Pairwise fun i j : Fin l => IsUnit
      (((σ.toRingEquiv : RingAut S) ^ (i : ℕ)) a - ((σ.toRingEquiv : RingAut S) ^ (j : ℕ)) a) := by
    simpa only [RingAut.coe_pow, AlgEquiv.coe_pow, AlgEquiv.coe_ringEquiv] using ha
  have hspan := span_cyclicSemilinear_fixed_eq_top (σ.toRingEquiv : RingAut S) D hl hD
    (semilinearVectorOperator_smul σ g) a hsep
  obtain ⟨c, hc⟩ := exists_generalLinear_columns_mem {x | D x = x} hspan
  refine ⟨c, ?_⟩
  have hmul : g * entrywiseAut σ n c = c := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (hc j : D (fun k => c k j) = (fun k => c k j)) i
  rw [mul_assoc, hmul, inv_mul_cancel]

end Langlands.BaseChange
