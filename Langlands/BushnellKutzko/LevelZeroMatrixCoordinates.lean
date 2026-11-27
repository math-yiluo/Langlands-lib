import Langlands.BushnellKutzko.LevelZeroTransport
import Langlands.BushnellKutzko.LevelZeroCoarse
import Langlands.BushnellKutzko.LevelZeroCuspidalSum
import Langlands.Representation.Classification.Supercuspidal

/-! # The adapted basis in standard coordinates of `F^n` -/

open ValuativeRel Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} (L : LatticeChain 𝒪[F] F (Fin n → F)) {e f : ℕ}
  (b : ∀ i : Fin e, Module.Basis (Fin f) 𝓀[F] (L.Layer ((i : ℕ) : ℤ)))
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (he : L.period = e)

/-- The matrix whose columns are the adapted basis vectors. -/
abbrev basisMat : Matrix (Fin n) (Fin f × Fin e) F :=
  (Pi.basisFun F (Fin n)).toMatrix (adaptedBasis L b hϖ he)

/-- The inverse of `basisMat`. -/
abbrev basisMatInv : Matrix (Fin f × Fin e) (Fin n) F :=
  (adaptedBasis L b hϖ he).toMatrix (Pi.basisFun F (Fin n))

theorem basisMat_mul_basisMatInv : basisMat L b hϖ he * basisMatInv L b hϖ he = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem basisMatInv_mul_basisMat : basisMatInv L b hϖ he * basisMat L b hϖ he = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- Matrices in the adapted basis, rewritten in the standard basis of `F^n`. -/
def stdToGL : GL (Fin f × Fin e) F ≃* GeneralLinear n F :=
  (stdToAut L b hϖ he).trans
    (Matrix.GeneralLinearGroup.toLin.symm :
      (Module.End F (Fin n → F))ˣ ≃* GeneralLinear n F)

theorem toLin_stdToGL (x : GL (Fin f × Fin e) F) :
    Matrix.GeneralLinearGroup.toLin (stdToGL L b hϖ he x) = stdToAut L b hϖ he x :=
  MulEquiv.apply_symm_apply _ _

theorem coe_stdToGL (x : GL (Fin f × Fin e) F) :
    ((stdToGL L b hϖ he x : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
      basisMat L b hϖ he * (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) *
        basisMatInv L b hϖ he := by
  have h1 : ((stdToGL L b hϖ he x : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
      LinearMap.toMatrix' ((stdToAut L b hϖ he x : (Module.End F (Fin n → F))ˣ) :
        Module.End F (Fin n → F)) := rfl
  rw [h1, coe_stdToAut, ← LinearMap.toMatrix_eq_toMatrix',
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (Pi.basisFun F (Fin n))
      (adaptedBasis L b hϖ he) (Pi.basisFun F (Fin n)) (adaptedBasis L b hϖ he),
    LinearMap.toMatrix_toLin]

theorem coe_stdToGL_symm (y : GeneralLinear n F) :
    (((stdToGL L b hϖ he).symm y : GL (Fin f × Fin e) F) :
        Matrix (Fin f × Fin e) (Fin f × Fin e) F) =
      basisMatInv L b hϖ he * (y : Matrix (Fin n) (Fin n) F) * basisMat L b hϖ he := by
  have h := coe_stdToGL L b hϖ he ((stdToGL L b hϖ he).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  simp only [← Matrix.mul_assoc]
  rw [basisMatInv_mul_basisMat, Matrix.one_mul, Matrix.mul_assoc, basisMatInv_mul_basisMat,
    Matrix.mul_one]

theorem continuous_stdToGL : Continuous (stdToGL L b hϖ he) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ (stdToGL L b hϖ he)) = fun x : GL (Fin f × Fin e) F =>
        basisMat L b hϖ he * (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) *
          basisMatInv L b hϖ he := funext (coe_stdToGL L b hϖ he)
    rw [h]
    exact (continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const
  · have h : (fun x : GL (Fin f × Fin e) F =>
        (((stdToGL L b hϖ he x)⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F)) =
        fun x : GL (Fin f × Fin e) F => basisMat L b hϖ he *
          ((x⁻¹ : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) *
            basisMatInv L b hϖ he :=
      funext fun x => by rw [← map_inv, coe_stdToGL]
    rw [h]
    exact (continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul continuous_const

theorem continuous_stdToGL_symm : Continuous (stdToGL L b hϖ he).symm := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ (stdToGL L b hϖ he).symm) = fun y : GeneralLinear n F =>
        basisMatInv L b hϖ he * (y : Matrix (Fin n) (Fin n) F) * basisMat L b hϖ he :=
      funext (coe_stdToGL_symm L b hϖ he)
    rw [h]
    exact (continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const
  · have h : (fun y : GeneralLinear n F =>
        ((((stdToGL L b hϖ he).symm y)⁻¹ : GL (Fin f × Fin e) F) :
          Matrix (Fin f × Fin e) (Fin f × Fin e) F)) =
        fun y : GeneralLinear n F => basisMatInv L b hϖ he *
          ((y⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * basisMat L b hϖ he :=
      funext fun y => by rw [← map_inv, coe_stdToGL_symm]
    rw [h]
    exact (continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul continuous_const

/-- `stdToGL` as an isomorphism of topological groups. -/
def stdToGLContinuous : GL (Fin f × Fin e) F ≃ₜ* GeneralLinear n F where
  toMulEquiv := stdToGL L b hϖ he
  continuous_toFun := continuous_stdToGL L b hϖ he
  continuous_invFun := continuous_stdToGL_symm L b hϖ he

/-- The numbering `(a, i) ↦ a + f i` of the indices, block after block. -/
def blockEquiv (hn : e * f = n) : Fin f × Fin e ≃ Fin n :=
  (Equiv.prodComm (Fin f) (Fin e)).trans (finProdFinEquiv.trans (finCongr hn))

theorem blockEquiv_val (hn : e * f = n) (p : Fin f × Fin e) :
    (blockEquiv hn p : ℕ) = p.1 + f * p.2 := by
  simp [blockEquiv, finProdFinEquiv]

theorem blockEquiv_lt_iff (hn : e * f = n) (p : Fin f × Fin e) :
    (blockEquiv hn p : ℕ) < f ↔ (p.2 : ℕ) = 0 := by
  rw [blockEquiv_val]
  constructor
  · intro h
    by_contra h0
    have : f ≤ f * p.2 := Nat.le_mul_of_pos_right f (Nat.pos_of_ne_zero h0)
    omega
  · intro h
    rw [h, mul_zero, add_zero]
    exact p.1.isLt

/-- The change of basis from the standard basis to the block-ordered adapted basis. -/
def changeGL (hn : e * f = n) : GeneralLinear n F :=
  ⟨(basisMat L b hϖ he).submatrix id (blockEquiv hn).symm,
    (basisMatInv L b hϖ he).submatrix (blockEquiv hn).symm id,
    by rw [Matrix.submatrix_mul_equiv, basisMat_mul_basisMatInv, Matrix.submatrix_id_id],
    mul_eq_one_comm.mp
      (by rw [Matrix.submatrix_mul_equiv, basisMat_mul_basisMatInv, Matrix.submatrix_id_id])⟩

theorem changeGL_conj (hn : e * f = n) (M : Matrix (Fin n) (Fin n) F) :
    ((changeGL L b hϖ he hn : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * M *
        (((changeGL L b hϖ he hn)⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
      basisMat L b hϖ he * M.submatrix (blockEquiv hn) (blockEquiv hn) *
        basisMatInv L b hϖ he := by
  have hM : M = (M.submatrix (blockEquiv hn) (blockEquiv hn)).submatrix (blockEquiv hn).symm
      (blockEquiv hn).symm := by
    simp [Matrix.submatrix_submatrix]
  change (basisMat L b hϖ he).submatrix id (blockEquiv hn).symm * M *
      (basisMatInv L b hϖ he).submatrix (blockEquiv hn).symm id = _
  conv_lhs => rw [hM]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

theorem stdToGL_reindex_symm (hn : e * f = n) (u : GeneralLinear n F) :
    stdToGL L b hϖ he ((GeneralLinear.reindex (blockEquiv hn)).symm u) =
      changeGL L b hϖ he hn * u * (changeGL L b hϖ he hn)⁻¹ := by
  ext1
  rw [coe_stdToGL, Units.val_mul, Units.val_mul, changeGL_conj]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation by the change of basis carries the unipotent radical of the standard parabolic
of shape `(f, n - f)` into the image of the coarse unipotent radical. -/
theorem reindex_symm_mem_coarseN (hn : e * f = n) (he0 : 0 < e) (hf : 0 < f) (hfn : f < n)
    {u : GeneralLinear n F} (hu : u ∈ (twoBlockShape hf hfn).unipotentSubgroup F) :
    (GeneralLinear.reindex (blockEquiv hn)).symm u ∈ coarseN F f he0 := by
  classical
  set x := (GeneralLinear.reindex (blockEquiv hn)).symm u with hxdef
  have hx : ∀ p q, (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q =
      (u : Matrix (Fin n) (Fin n) F) (blockEquiv hn p) (blockEquiv hn q) := fun _ _ => rfl
  have key : ∀ p q : Fin f × Fin e, ¬ ((p.2 : ℕ) = 0 ∧ (q.2 : ℕ) ≠ 0) →
      (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q =
        (1 : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q := by
    intro p q hpq
    rw [hx, twoBlock_unipotent_entry hf hfn hu]
    · by_cases h : p = q
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
        exact fun h' => h ((blockEquiv hn).injective h')
    · rw [blockEquiv_lt_iff, ← not_lt, blockEquiv_lt_iff]
      exact hpq
  let X : Matrix (TopIx f he0) (RstIx f he0) F :=
    Matrix.of fun i j => (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) i.1 j.1
  refine ⟨Multiplicative.ofAdd X, ?_⟩
  ext s t
  change ((upperHom (Multiplicative.ofAdd X) : GL (TopIx f he0 ⊕ RstIx f he0) F) :
      Matrix (TopIx f he0 ⊕ RstIx f he0) (TopIx f he0 ⊕ RstIx f he0) F) s t =
    ((coarseReindex F f he0 x : GL (TopIx f he0 ⊕ RstIx f he0) F) :
      Matrix (TopIx f he0 ⊕ RstIx f he0) (TopIx f he0 ⊕ RstIx f he0) F) s t
  rw [coe_upperHom, coe_coarseReindex_apply]
  have h0 : ∀ p : Fin f × Fin e, p.2 = ⟨0, he0⟩ ↔ (p.2 : ℕ) = 0 := fun p => by
    rw [Fin.ext_iff]
  rcases s with i | i <;> rcases t with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.submatrix_apply]
    change (1 : Matrix (TopIx f he0) (TopIx f he0) F) i j = x i.1 j.1
    rw [key _ _ (fun h => h.2 ((h0 _).mp j.2))]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.submatrix_apply]
    rfl
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply, Matrix.zero_apply]
    change (0 : F) = x i.1 j.1
    rw [key _ _ (fun h => i.2 ((h0 _).mpr h.1)), Matrix.one_apply_ne]
    intro h
    exact i.2 (h ▸ j.2)
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply]
    change (1 : Matrix (RstIx f he0) (RstIx f he0) F) i j = x i.1 j.1
    rw [key _ _ (fun h => i.2 ((h0 _).mpr h.1))]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]

/-- Every element of the conjugated unipotent radical is the image of an element of the
coarse unipotent radical. -/
theorem exists_mem_coarseN_of_mem_conjugateUnipotent (hn : e * f = n) (he0 : 0 < e)
    (hf : 0 < f) (hfn : f < n) {y : GeneralLinear n F}
    (hy : y ∈ (twoBlockShape hf hfn).conjugateUnipotent (changeGL L b hϖ he hn)) :
    ∃ x ∈ coarseN F f he0, stdToGL L b hϖ he x = y := by
  obtain ⟨u, hu, rfl⟩ := hy
  exact ⟨_, reindex_symm_mem_coarseN hn he0 hf hfn hu, stdToGL_reindex_symm L b hϖ he hn u⟩

end Langlands.BushnellKutzko.LevelZero
