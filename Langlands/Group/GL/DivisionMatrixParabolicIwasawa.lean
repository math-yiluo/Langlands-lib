import Langlands.Group.GL.DivisionMatrixIwasawa
import Langlands.Cohomology.Continuous.InnerConjugation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Compact factorization for an idempotent parabolic over a division ring -/

noncomputable section

namespace Langlands.GeneralLinearGroup

open Matrix Module Set

universe u

variable {D : Type u} [DivisionRing D]

private abbrev squareMatrix (n : ℕ) := Matrix (Fin n) (Fin n) D

private def firstBlockIdempotent (n r : ℕ) : squareMatrix (D := D) n :=
  Matrix.diagonal fun i => if i.val < r then 1 else 0

private theorem exists_conj_firstBlock {n : ℕ} (e : squareMatrix (D := D) n)
    (he : IsIdempotentElem e) :
    ∃ (u : (squareMatrix (D := D) n)ˣ) (r : ℕ),
      u.val * e * u.inv = firstBlockIdempotent n r := by
  classical
  let T : Module.End D (Fin n → D) := e.toLinearMapRight'
  have hT : IsIdempotentElem T := by
    change T.comp T = T
    change e.toLinearMapRight' ∘ₗ e.toLinearMapRight' = e.toLinearMapRight'
    rw [← Matrix.toLinearMapRight'_mul, he.eq]
  let P := LinearMap.range T
  let Q := LinearMap.ker T
  have hPQ : IsCompl P Q := LinearMap.IsIdempotentElem.isCompl hT
  let r := finrank D P
  let s := finrank D Q
  have hrs : r + s = n := (Submodule.finrank_add_eq_of_isCompl hPQ).trans
    (Module.finrank_fin_fun (R := D))
  let indices : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let split : (Fin n → D) ≃ₗ[D] (Fin r → D) × (Fin s → D) :=
    (LinearEquiv.piCongrLeft' D (fun _ : Fin n => D) indices.symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) D D)
  let p := (Module.finBasis D P).equivFun.symm
  let q := (Module.finBasis D Q).equivFun.symm
  let B := (p.prodCongr q).trans (Submodule.prodEquivOfIsCompl P Q hPQ)
  let L := split.trans B
  have hleft (i : Fin r) : (indices (Sum.inl i)).val < r := by
    simp [indices]
  have hright (i : Fin s) : ¬ (indices (Sum.inr i)).val < r := by
    simp [indices]
  let d : squareMatrix (D := D) n := firstBlockIdempotent n r
  have hsplit (x : Fin n → D) : split (x ᵥ* d) = ((split x).1, 0) := by
    apply Prod.ext <;> funext i
    · change (x ᵥ* d) (indices (Sum.inl i)) = x (indices (Sum.inl i))
      simp [d, firstBlockIdempotent, vecMul_diagonal, hleft]
    · change (x ᵥ* d) (indices (Sum.inr i)) = 0
      simp [d, firstBlockIdempotent, vecMul_diagonal, hright]
  have hL (x : Fin n → D) : T (L x) = L (x ᵥ* d) := by
    change T (B (split x)) = B (split (x ᵥ* d))
    rw [hsplit]
    have hp : T (p (split x).1 : Fin n → D) = p (split x).1 :=
      (LinearMap.IsIdempotentElem.mem_range_iff hT).mp (p (split x).1).property
    have hq : T (q (split x).2 : Fin n → D) = 0 :=
      LinearMap.mem_ker.mp (q (split x).2).property
    change T ((p (split x).1 : Fin n → D) + (q (split x).2 : Fin n → D)) =
      (p (split x).1 : Fin n → D) + (q 0 : Fin n → D)
    simp only [map_add, hp, hq, map_zero, Submodule.coe_zero]
  let a := L.toLinearMap.toMatrixRight'
  let b := L.symm.toLinearMap.toMatrixRight'
  have hab : a * b = 1 := by
    change L.toLinearMap.toMatrixRight' * L.symm.toLinearMap.toMatrixRight' = _
    rw [← LinearMap.toMatrixRight'_comp, ← LinearMap.toMatrixRight'_id]
    exact congrArg (LinearMap.toMatrixRight') (LinearMap.ext L.symm_apply_apply)
  have hba : b * a = 1 := by
    change L.symm.toLinearMap.toMatrixRight' * L.toLinearMap.toMatrixRight' = _
    rw [← LinearMap.toMatrixRight'_comp, ← LinearMap.toMatrixRight'_id]
    exact congrArg (LinearMap.toMatrixRight') (LinearMap.ext L.apply_symm_apply)
  have hae : a * e = d * a := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_mul]
    apply LinearMap.ext
    intro x
    change T (Matrix.toLinearMapRight' (LinearMap.toMatrixRight' L.toLinearMap) x) =
      Matrix.toLinearMapRight' (LinearMap.toMatrixRight' L.toLinearMap) (x ᵥ* d)
    rw [LinearEquiv.symm_apply_apply]
    exact hL x
  refine ⟨⟨a, b, hab, hba⟩, r, ?_⟩
  change a * e * b = d
  rw [hae, mul_assoc, hab, mul_one]

private theorem corner_eq_zero_of_upperTriangular {n : ℕ} (r : ℕ)
    (g : squareMatrix (D := D) n) (hg : g.IsUpperTriangular) :
    (1 - firstBlockIdempotent n r) * g * firstBlockIdempotent n r = 0 := by
  unfold firstBlockIdempotent
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val < r
  · simp [hi]
  · by_cases hj : j.val < r
    · have hji : j < i := hj.trans_le (le_of_not_gt hi)
      simp [hj, hg hji]
    · simp [hj]

variable [TopologicalSpace D] (O : Subring D) (v : AbsoluteValue D ℝ)

/-- A compact open unit ball gives compact Iwasawa factorization for every idempotent
parabolic of a matrix algebra over a division ring. -/
def DivisionMatrixParabolicIwasawaStatement : Prop :=
  IsCompact (O : Set D) → IsOpen (O : Set D) → (∀ a : D, a ∈ O ↔ v a ≤ 1) →
    ∀ (n : ℕ) (e : squareMatrix (D := D) n), IsIdempotentElem e →
      ∃ K : OpenSubgroup (squareMatrix (D := D) n)ˣ,
        IsCompact (K : Set (squareMatrix (D := D) n)ˣ) ∧
        ∀ g : (squareMatrix (D := D) n)ˣ, ∃ p : (squareMatrix (D := D) n)ˣ,
          (1 - e) * p.val * e = 0 ∧ ∃ k ∈ K, g = p * k

theorem divisionMatrixParabolicIwasawa [IsTopologicalRing D] [T2Space D] :
    DivisionMatrixParabolicIwasawaStatement O v := by
  intro hOc hOo hO n e he
  obtain ⟨u, r, hur⟩ := exists_conj_firstBlock e he
  let K₀ : OpenSubgroup (squareMatrix (D := D) n)ˣ :=
    ⟨(O.matrix (n := Fin n)).toSubmonoid.units, Submonoid.isOpen_units hOo.matrix⟩
  have hK₀ : IsCompact (K₀ : Set (squareMatrix (D := D) n)ˣ) :=
    Submonoid.units_isCompact hOc.matrix
  let C := Langlands.Continuous.innerConjugationEquiv u
  let K := K₀.comap C.toMonoidHom C.continuous
  refine ⟨K, C.toHomeomorph.isCompact_preimage.mpr hK₀, ?_⟩
  intro g
  obtain ⟨k₀, hk₀, hup⟩ := divisionMatrixIwasawa O v hO n (C g)
  let p := C.symm (C g * k₀)
  let k := C.symm k₀⁻¹
  have hk : k ∈ K := by
    change C (C.symm k₀⁻¹) ∈ K₀
    rw [C.apply_symm_apply]
    exact K₀.inv_mem hk₀
  let φ := MulSemiringAction.toRingEquiv (ConjAct (squareMatrix (D := D) n)ˣ)
    (squareMatrix (D := D) n) (ConjAct.toConjAct u)
  have hφ : φ e = firstBlockIdempotent n r := hur
  have hp : φ p.val = (C g * k₀).val := by
    change (C p).val = _
    rw [C.apply_symm_apply]
  have hz : (1 - e) * p.val * e = 0 := by
    apply φ.injective
    rw [map_mul, map_mul, map_sub, map_one, map_zero, hφ, hp]
    exact corner_eq_zero_of_upperTriangular r _ hup
  refine ⟨p, hz, k, hk, C.injective ?_⟩
  rw [map_mul, C.apply_symm_apply, C.apply_symm_apply, mul_inv_cancel_right]

end Langlands.GeneralLinearGroup
