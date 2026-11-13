import Langlands.GroupScheme.Examples.HermitianLocalIsotropy
import Langlands.GroupScheme.Examples.HermitianMatrixRootComparison

/-! # Local Hermitian presentations identify the actual root model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {m : ℕ}

namespace Form

/-- Over a separable quadratic extension of a nonarchimedean local field, every
nonsingular Hermitian form on `HermitianRoot.Index (Fin m)` with `1 ≤ m` is the
congruence transform of a hyperbolic-plus-diagonal Gram matrix with nonzero
weights, in the convention of `Presentation.rootIsometryIso`. -/
theorem exists_local_root_congruence (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m)))
    (hm : 1 ≤ m) :
    ∃ H : HermitianRoot.DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ Q : Matrix.GeneralLinearGroup (HermitianRoot.Index (Fin m)) L,
        adjoint (fieldInvolution K L)
            (Q : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) *
          HermitianRoot.gram H *
            (Q : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) =
          J.gram := by
  have hdet : (J.gram : Matrix (HermitianRoot.Index (Fin m))
      (HermitianRoot.Index (Fin m)) L).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit J.gram)).ne_zero
  obtain ⟨H, hH, P, hP⟩ := HermitianRoot.local_exists_gram_congruence (K := K) m hm
    (J.gram : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L)
    J.hermitian hdet
  refine ⟨H, hH, P⁻¹, ?_⟩
  have hpq : (P : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) *
      ((P⁻¹ : Matrix.GeneralLinearGroup (HermitianRoot.Index (Fin m)) L) :
        Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← hP]
  change adjoint (fieldInvolution K L) _ *
      (adjoint (fieldInvolution K L) _ * _ * _) * _ = _
  calc
    _ = adjoint (fieldInvolution K L)
          ((P : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) *
            ((P⁻¹ : Matrix.GeneralLinearGroup (HermitianRoot.Index (Fin m)) L) :
              Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L)) *
          (J.gram : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) *
          ((P : Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L) *
            ((P⁻¹ : Matrix.GeneralLinearGroup (HermitianRoot.Index (Fin m)) L) :
              Matrix (HermitianRoot.Index (Fin m)) (HermitianRoot.Index (Fin m)) L)) := by
      rw [adjoint_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hpq, adjoint_one, Matrix.one_mul, Matrix.mul_one]

/-- The chosen local diagonal middle form of a nonsingular Hermitian form on
`HermitianRoot.Index (Fin m)`, `1 ≤ m`. -/
def localRootForm (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m)))
    (hm : 1 ≤ m) : HermitianRoot.DiagonalForm (fieldInvolution K L) (Fin m) :=
  Classical.choose (J.exists_local_root_congruence hm)

theorem localRootForm_weight_ne_zero
    (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m))) (hm : 1 ≤ m)
    (i : Fin m) : (J.localRootForm hm).weight i ≠ 0 :=
  (Classical.choose_spec (J.exists_local_root_congruence hm)).1 i

/-- The weights of the chosen local diagonal middle form, as units. -/
def localRootUnits (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m)))
    (hm : 1 ≤ m) (i : Fin m) : Lˣ :=
  Units.mk0 ((J.localRootForm hm).weight i) (J.localRootForm_weight_ne_zero hm i)

@[simp] theorem localRootUnits_val
    (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m))) (hm : 1 ≤ m)
    (i : Fin m) : (J.localRootUnits hm i : L) = (J.localRootForm hm).weight i := rfl

/-- The chosen invertible matrix carrying the hyperbolic-plus-diagonal Gram matrix
of `localRootForm` to the given Gram matrix. -/
def localRootMatrix (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m)))
    (hm : 1 ≤ m) : Matrix.GeneralLinearGroup (HermitianRoot.Index (Fin m)) L :=
  Classical.choose (Classical.choose_spec (J.exists_local_root_congruence hm)).2

theorem localRootMatrix_spec
    (J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m))) (hm : 1 ≤ m) :
    adjoint (fieldInvolution K L)
        (J.localRootMatrix hm : Matrix (HermitianRoot.Index (Fin m))
          (HermitianRoot.Index (Fin m)) L) *
      HermitianRoot.gram (J.localRootForm hm) *
        (J.localRootMatrix hm : Matrix (HermitianRoot.Index (Fin m))
          (HermitianRoot.Index (Fin m)) L) = J.gram :=
  Classical.choose_spec (Classical.choose_spec (J.exists_local_root_congruence hm)).2

end Form

namespace SchemeModel.Presentation

variable {G : GroupScheme (Spec (CommRingCat.of K))}

/-- A presentation of `G` by a nonsingular Hermitian form on
`HermitianRoot.Index (Fin m)`, `1 ≤ m`, over a local field identifies `G` with the
actual Hermitian root model of the chosen local diagonal middle form. -/
def localRootIso {J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m))}
    (e : Presentation K L J G) (hm : 1 ≤ m) :
    G ≅ HermitianRoot.SchemeModel.groupScheme K L (J.localRootForm hm)
      (J.localRootUnits hm) (J.localRootUnits_val hm) :=
  e.rootIsometryIso (J.localRootForm hm) (J.localRootUnits hm) (J.localRootUnits_val hm)
    (J.localRootMatrix hm) (J.localRootMatrix_spec hm)

/-- Over a local field, a presentation of `G` by a nonsingular Hermitian form on
any finite type with `m + 2` elements, `1 ≤ m`, gives an isomorphism of `G` with an
actual Hermitian root model whose diagonal middle has `m` coordinates. -/
theorem exists_local_rootIso {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
    {J : Form (fieldInvolution K L) Idx} (e : Presentation K L J G) (hm : 1 ≤ m)
    (hcard : Fintype.card Idx = m + 2) :
    ∃ (H : HermitianRoot.DiagonalForm (fieldInvolution K L) (Fin m)) (w : Fin m → Lˣ)
      (hw : ∀ i, (w i : L) = H.weight i),
      Nonempty (G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw) := by
  have hc : Fintype.card Idx = Fintype.card (HermitianRoot.Index (Fin m)) := by
    rw [hcard]
    simp only [HermitianRoot.Index, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    omega
  let r : Idx ≃ HermitianRoot.Index (Fin m) := Fintype.equivOfCardEq hc
  exact ⟨_, _, _, ⟨(e.reindex r).localRootIso hm⟩⟩

/-- The form of `exists_local_rootIso` used for type `A_n`: a presentation by a
nonsingular Hermitian form on `n + 1` coordinates, `2 ≤ n`, gives an isomorphism of
`G` with an actual Hermitian root model whose middle is indexed by `Fin (n - 1)`. -/
theorem exists_local_rootIso_of_card_eq_succ {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
    {J : Form (fieldInvolution K L) Idx} (e : Presentation K L J G) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card Idx = n + 1) :
    ∃ (H : HermitianRoot.DiagonalForm (fieldInvolution K L) (Fin (n - 1)))
      (w : Fin (n - 1) → Lˣ) (hw : ∀ i, (w i : L) = H.weight i),
      Nonempty (G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw) :=
  e.exists_local_rootIso (m := n - 1) (by omega) (by omega)

end SchemeModel.Presentation

end Langlands.GroupScheme.HermitianMatrix
