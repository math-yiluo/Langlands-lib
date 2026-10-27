import Langlands.Group.GL.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Ordered block parabolics of actual general linear groups
-/

namespace Langlands.GeneralLinear

universe u

/-- Positive ordered block sizes with their total rank. -/
structure BlockShape (n : ℕ) where
  length : ℕ
  size : Fin length → ℕ
  positive : ∀ i, 0 < size i
  sum_eq : ∑ i, size i = n

namespace BlockShape

variable {n : ℕ} (B : BlockShape n)

/-- A block shape has at most as many blocks as its total rank. -/
theorem length_le : B.length ≤ n := by
  calc B.length = ∑ _i : Fin B.length, 1 := by simp
    _ ≤ ∑ i, B.size i := Finset.sum_le_sum fun i _ => B.positive i
    _ = n := B.sum_eq

/-- Coordinates indexed first by their block, then by their position in it. -/
abbrev Index := (i : Fin B.length) × Fin (B.size i)

/-- The standard consecutive-block numbering, in the given block order. -/
def indexEquiv : B.Index ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr B.sum_eq)

/-- Include a coordinate of one block into the total rank. -/
def index (i : Fin B.length) : Fin (B.size i) ↪ Fin n :=
  ⟨fun j => B.indexEquiv ⟨i, j⟩,
    fun _ _ h => Sigma.mk.inj_iff.mp (B.indexEquiv.injective h) |>.2 |> eq_of_heq⟩

variable (R : Type u) [CommRing R]

/-- The Levi product consists of the actual general linear group of each block. -/
abbrev Levi := ∀ i : Fin B.length, Langlands.GeneralLinear (B.size i) R

private def triangularSubgroup {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder α] (b : ι → α) : Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {g | Matrix.BlockTriangular (g : Matrix ι ι R) b}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := ha.mul hb
  inv_mem' := by
    intro g hg
    let := g.invertible
    change Matrix.BlockTriangular ((g⁻¹ : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) b
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

/-- Upper block triangular matrices in block coordinates. -/
def sigmaParabolic : Subgroup (Matrix.GeneralLinearGroup B.Index R) :=
  triangularSubgroup R Sigma.fst

/-- The standard upper block parabolic as a subgroup of actual `GL_n(R)`. -/
def parabolic : Subgroup (Langlands.GeneralLinear n R) :=
  (B.sigmaParabolic R).comap (reindex (R := R) B.indexEquiv).symm.toMonoidHom

/-- The opposite, lower block parabolic in the same standard coordinates. -/
def oppositeParabolic : Subgroup (Langlands.GeneralLinear n R) :=
  (triangularSubgroup R (fun a : B.Index => OrderDual.toDual a.1)).comap
    (reindex (R := R) B.indexEquiv).symm.toMonoidHom

/-- The block diagonal homomorphism, in block coordinates. -/
def sigmaLeviEmbedding : B.Levi R →* Matrix.GeneralLinearGroup B.Index R :=
  (Units.map (Matrix.blockDiagonal'RingHom (fun i => Fin (B.size i)) R).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

/-- The block diagonal homomorphism into actual `GL_n(R)`. -/
def leviEmbedding : B.Levi R →* Langlands.GeneralLinear n R :=
  (reindex (R := R) B.indexEquiv).toMonoidHom.comp (B.sigmaLeviEmbedding R)

/-- Extract a diagonal block from a matrix in block coordinates. -/
def diagonalBlock (A : Matrix B.Index B.Index R) (i : Fin B.length) :
    Matrix (Fin (B.size i)) (Fin (B.size i)) R :=
  A.submatrix (fun j => (⟨i, j⟩ : B.Index)) (fun j => (⟨i, j⟩ : B.Index))

private theorem diagonalBlock_one (i : Fin B.length) :
    B.diagonalBlock R 1 i = 1 := by
  ext a b
  simp [diagonalBlock, Matrix.one_apply]

private theorem diagonalBlock_mul
    {A C : Matrix B.Index B.Index R}
    (hA : A.BlockTriangular Sigma.fst) (hC : C.BlockTriangular Sigma.fst)
    (i : Fin B.length) :
    B.diagonalBlock R (A * C) i =
      B.diagonalBlock R A i * B.diagonalBlock R C i := by
  ext a b
  simp only [diagonalBlock, Matrix.submatrix_apply, Matrix.mul_apply,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single i]
  intro j hji
  apply Finset.sum_eq_zero
  intro k _
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-- Extract the invertible diagonal blocks of an upper block triangular matrix.
The inverse of each block is extracted from the inverse of the original matrix. -/
def sigmaLeviProjection : B.sigmaParabolic R →* B.Levi R where
  toFun g i :=
    { val := B.diagonalBlock R g.val.val i
      inv := B.diagonalBlock R ((g.val⁻¹ : Matrix.GeneralLinearGroup B.Index R).val) i
      val_inv := by
        rw [← B.diagonalBlock_mul R g.property ((B.sigmaParabolic R).inv_mem g.property) i]
        rw [g.val.mul_inv]
        exact B.diagonalBlock_one R i
      inv_val := by
        rw [← B.diagonalBlock_mul R ((B.sigmaParabolic R).inv_mem g.property) g.property i]
        rw [g.val.inv_mul]
        exact B.diagonalBlock_one R i }
  map_one' := by
    funext i
    apply Units.ext
    change B.diagonalBlock R 1 i = 1
    exact B.diagonalBlock_one R i
  map_mul' g h := by
    funext i
    apply Units.ext
    exact B.diagonalBlock_mul R g.property h.property i

/-- The explicit equivalence between standard and block parabolic coordinates. -/
def parabolicCoordinates : B.parabolic R ≃* B.sigmaParabolic R where
  toFun g := ⟨(reindex (R := R) B.indexEquiv).symm g.val, g.property⟩
  invFun g := ⟨reindex (R := R) B.indexEquiv g.val, by
    change (reindex (R := R) B.indexEquiv).symm
      (reindex (R := R) B.indexEquiv g.val) ∈ B.sigmaParabolic R
    simpa only [MulEquiv.symm_apply_apply] using g.property⟩
  left_inv g := Subtype.ext ((reindex (R := R) B.indexEquiv).apply_symm_apply g.val)
  right_inv g := Subtype.ext ((reindex (R := R) B.indexEquiv).symm_apply_apply g.val)
  map_mul' g h := Subtype.ext ((reindex (R := R) B.indexEquiv).symm.map_mul g.val h.val)

/-- The diagonal block projection in standard coordinates. -/
def leviProjection : B.parabolic R →* B.Levi R :=
  (B.sigmaLeviProjection R).comp (B.parabolicCoordinates R).toMonoidHom

private def sigmaLeviInParabolic : B.Levi R →* B.sigmaParabolic R :=
  (B.sigmaLeviEmbedding R).codRestrict _ fun m =>
    Matrix.blockTriangular_blockDiagonal' (fun i => (m i).val)

/-- The block diagonal section of the Levi projection, valued in the parabolic. -/
def leviInParabolic : B.Levi R →* B.parabolic R :=
  (B.parabolicCoordinates R).symm.toMonoidHom.comp (B.sigmaLeviInParabolic R)

@[simp] theorem leviInParabolic_val (m : B.Levi R) :
    (B.leviInParabolic R m).val = B.leviEmbedding R m := rfl

private theorem sigmaLeviProjection_section (m : B.Levi R) :
    B.sigmaLeviProjection R (B.sigmaLeviInParabolic R m) = m := by
  funext i
  apply Units.ext
  ext a b
  change Matrix.blockDiagonal' (fun j => (m j).val) ⟨i, a⟩ ⟨i, b⟩ = (m i).val a b
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _

@[simp] theorem leviProjection_section (m : B.Levi R) :
    B.leviProjection R (B.leviInParabolic R m) = m := by
  change B.sigmaLeviProjection R
    (B.parabolicCoordinates R ((B.parabolicCoordinates R).symm
      (B.sigmaLeviInParabolic R m))) = m
  rw [MulEquiv.apply_symm_apply]
  exact B.sigmaLeviProjection_section R m

/-- The block upper unipotent radical, as a subgroup of the actual parabolic. -/
def unipotentRadical : Subgroup (B.parabolic R) :=
  (B.leviProjection R).ker

instance unipotentRadicalNormal : (B.unipotentRadical R).Normal :=
  inferInstanceAs (B.leviProjection R).ker.Normal

/-- The same radical included as a matrix subgroup of the full general linear group. -/
def unipotentSubgroup : Subgroup (Langlands.GeneralLinear n R) :=
  (B.unipotentRadical R).map (B.parabolic R).subtype

/-- Conjugation by the embedded Levi factor on the normal unipotent radical. -/
def leviAction : B.Levi R →* MulAut (B.unipotentRadical R) :=
  MulAut.conjNormal.comp (B.leviInParabolic R)

/-- Remove the diagonal-block part by multiplication on the right. -/
def unipotentPart (g : B.parabolic R) : B.unipotentRadical R :=
  ⟨g * (B.leviInParabolic R (B.leviProjection R g))⁻¹, by
    change B.leviProjection R (g * (B.leviInParabolic R (B.leviProjection R g))⁻¹) = 1
    simp⟩

/-- The unique factorization `g = u * m` is constructed, not assumed. -/
def decomposition : B.parabolic R ≃ B.unipotentRadical R × B.Levi R where
  toFun g := (B.unipotentPart R g, B.leviProjection R g)
  invFun um := um.1.val * B.leviInParabolic R um.2
  left_inv g := by
    exact inv_mul_cancel_right _ _
  right_inv um := by
    rcases um with ⟨u, m⟩
    have hu : B.leviProjection R u.val = 1 := u.property
    have hp : B.leviProjection R (u.val * B.leviInParabolic R m) = m := by
      simp [hu]
    apply Prod.ext
    · apply Subtype.ext
      change u.val * B.leviInParabolic R m *
        (B.leviInParabolic R (B.leviProjection R (u.val * B.leviInParabolic R m)))⁻¹ = u.val
      rw [hp, mul_inv_cancel_right]
    · exact hp

/-- In standard coordinates, precisely the blocks strictly below the diagonal vanish. -/
theorem mem_parabolic_iff (g : Langlands.GeneralLinear n R) :
    g ∈ B.parabolic R ↔
      ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)),
        j < i → g (B.index i a) (B.index j b) = 0 := by
  constructor
  · intro hg i j a b hij
    exact hg (i := ⟨i, a⟩) (j := ⟨j, b⟩) hij
  · intro hg
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    exact hg i j a b hij

/-- The opposite parabolic has zero blocks strictly above the diagonal. -/
theorem mem_oppositeParabolic_iff (g : Langlands.GeneralLinear n R) :
    g ∈ B.oppositeParabolic R ↔
      ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)),
        i < j → g (B.index i a) (B.index j b) = 0 := by
  constructor
  · intro hg i j a b hij
    exact hg (i := ⟨i, a⟩) (j := ⟨j, b⟩) hij
  · intro hg
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    exact hg i j a b hij

/-- The Levi embedding preserves the entries of each diagonal block. -/
@[simp] theorem leviEmbedding_apply_same (m : B.Levi R) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    B.leviEmbedding R m (B.index i a) (B.index i b) = m i a b := by
  change Matrix.blockDiagonal' (fun j => (m j).val)
    (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩))
    (B.indexEquiv.symm (B.indexEquiv ⟨i, b⟩)) = _
  simp only [Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]

/-- The Levi embedding has zero entries between distinct blocks. -/
theorem leviEmbedding_apply_ne (m : B.Levi R) {i j : Fin B.length}
    (a : Fin (B.size i)) (b : Fin (B.size j)) (hij : i ≠ j) :
    B.leviEmbedding R m (B.index i a) (B.index j b) = 0 := by
  change Matrix.blockDiagonal' (fun k => (m k).val)
    (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩))
    (B.indexEquiv.symm (B.indexEquiv ⟨j, b⟩)) = 0
  simp only [Equiv.symm_apply_apply]
  exact Matrix.blockDiagonal'_apply_ne (fun k => (m k).val) a b hij

/-- The Levi projection extracts the actual diagonal submatrices. -/
@[simp] theorem leviProjection_apply (g : B.parabolic R) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    B.leviProjection R g i a b = g.val (B.index i a) (B.index i b) := rfl

/-- The block diagonal map is injective, since its section is split by projection. -/
theorem leviEmbedding_injective : Function.Injective (B.leviEmbedding R) := by
  intro a b h
  have hs : B.leviInParabolic R a = B.leviInParabolic R b := Subtype.ext h
  simpa only [leviProjection_section] using congrArg (B.leviProjection R) hs

/-- The actual block diagonal matrix subgroup. -/
def leviSubgroup : Subgroup (Langlands.GeneralLinear n R) :=
  (B.leviEmbedding R).range

/-- Include the block diagonal matrix subgroup in the parabolic. -/
def leviAsParabolic : B.leviSubgroup R →* B.parabolic R where
  toFun g := ⟨g.val, by
    rcases g.property with ⟨m, hm⟩
    rw [← hm]
    exact (B.leviInParabolic R m).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The product Levi is isomorphic to its actual block diagonal image;
the inverse is the proved diagonal-block projection. -/
def leviEquiv : B.Levi R ≃* B.leviSubgroup R where
  toFun m := ⟨B.leviEmbedding R m, ⟨m, rfl⟩⟩
  invFun g := B.leviProjection R (B.leviAsParabolic R g)
  left_inv m := B.leviProjection_section R m
  right_inv := by
    rintro ⟨g, m, rfl⟩
    apply Subtype.ext
    change B.leviEmbedding R (B.leviProjection R (B.leviInParabolic R m)) =
      B.leviEmbedding R m
    rw [leviProjection_section]
  map_mul' a b := Subtype.ext ((B.leviEmbedding R).map_mul a b)

/-- The radical consists exactly of parabolic matrices with identity diagonal blocks. -/
theorem mem_unipotentRadical_iff (g : B.parabolic R) :
    g ∈ B.unipotentRadical R ↔
      ∀ (i : Fin B.length) (a b : Fin (B.size i)),
        g.val (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  change B.leviProjection R g = 1 ↔ _
  constructor
  · intro hg i a b
    have h := congrArg (fun m : B.Levi R => m i a b) hg
    simpa only [leviProjection_apply, Pi.one_apply,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] using h
  · intro hg
    funext i
    apply Units.ext
    ext a b
    exact hg i a b

/-- Membership in the ambient radical image has the same intrinsic matrix description. -/
theorem mem_unipotentSubgroup_iff (g : Langlands.GeneralLinear n R) :
    g ∈ B.unipotentSubgroup R ↔
      g ∈ B.parabolic R ∧
        ∀ (i : Fin B.length) (a b : Fin (B.size i)),
          g (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, (B.mem_unipotentRadical_iff R h).mp hh⟩
  · rintro ⟨hg, hd⟩
    exact ⟨⟨g, hg⟩, (B.mem_unipotentRadical_iff R ⟨g, hg⟩).mpr hd, rfl⟩

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Changing parabolic coordinates preserves the actual subgroup topologies. -/
def parabolicCoordinatesContinuous : B.parabolic R ≃ₜ* B.sigmaParabolic R where
  toMulEquiv := B.parabolicCoordinates R
  continuous_toFun :=
    ((reindexContinuous (R := R) B.indexEquiv).symm.continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((reindexContinuous (R := R) B.indexEquiv).continuous.comp
      continuous_subtype_val).subtype_mk _

omit [IsTopologicalRing R] in
private theorem continuous_sigmaLeviEmbedding : Continuous (B.sigmaLeviEmbedding R) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun m : B.Levi R => Matrix.blockDiagonal' (fun i => (m i).val))
    apply Continuous.matrix_blockDiagonal'
    apply continuous_pi
    intro i
    exact Units.continuous_val.comp (continuous_apply i)
  · change Continuous
      (fun m : B.Levi R => Matrix.blockDiagonal' (fun i => ((m i)⁻¹).val))
    apply Continuous.matrix_blockDiagonal'
    apply continuous_pi
    intro i
    exact Units.continuous_coe_inv.comp (continuous_apply i)

/-- The actual block diagonal embedding is continuous. -/
def leviEmbeddingContinuous : ContinuousMonoidHom (B.Levi R) (Langlands.GeneralLinear n R) where
  toMonoidHom := B.leviEmbedding R
  continuous_toFun :=
    (reindexContinuous (R := R) B.indexEquiv).continuous.comp
      (B.continuous_sigmaLeviEmbedding R)

private theorem continuous_sigmaLeviProjection : Continuous (B.sigmaLeviProjection R) := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g : B.sigmaParabolic R => B.diagonalBlock R g.val.val i)
    apply continuous_matrix
    intro a b
    exact (continuous_apply (⟨i, b⟩ : B.Index)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_subtype_val (⟨i, a⟩ : B.Index))
  · change Continuous (fun g : B.sigmaParabolic R =>
      B.diagonalBlock R ((g.val⁻¹ : Matrix.GeneralLinearGroup B.Index R).val) i)
    apply continuous_matrix
    intro a b
    exact (continuous_apply (⟨i, b⟩ : B.Index)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _
        (continuous_inv.comp continuous_subtype_val) (⟨i, a⟩ : B.Index))

/-- The actual diagonal-block projection is continuous. -/
def leviProjectionContinuous : ContinuousMonoidHom (B.parabolic R) (B.Levi R) where
  toMonoidHom := B.leviProjection R
  continuous_toFun :=
    (B.continuous_sigmaLeviProjection R).comp (B.parabolicCoordinatesContinuous R).continuous

/-- The block diagonal section is continuous for the subgroup topology. -/
def leviInParabolicContinuous : ContinuousMonoidHom (B.Levi R) (B.parabolic R) where
  toMonoidHom := B.leviInParabolic R
  continuous_toFun := (B.leviEmbeddingContinuous R).continuous.subtype_mk _

/-- The Levi product carries exactly the topology of its block diagonal matrix image. -/
def leviEquivContinuous : B.Levi R ≃ₜ* B.leviSubgroup R where
  toMulEquiv := B.leviEquiv R
  continuous_toFun := (B.leviEmbeddingContinuous R).continuous.subtype_mk _
  continuous_invFun := (B.leviProjectionContinuous R).continuous.comp
    (continuous_subtype_val.subtype_mk _)

/-- The proved `u*m` factorization is a homeomorphism. -/
def decompositionHomeomorph : B.parabolic R ≃ₜ B.unipotentRadical R × B.Levi R where
  toEquiv := B.decomposition R
  continuous_toFun :=
    ((continuous_id.mul ((B.leviInParabolicContinuous R).continuous.comp
      (B.leviProjectionContinuous R).continuous).inv).subtype_mk _).prodMk
        (B.leviProjectionContinuous R).continuous
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((B.leviInParabolicContinuous R).continuous.comp continuous_snd)

/-- The Levi conjugation action is jointly continuous. -/
theorem continuous_leviAction :
    Continuous (fun mu : B.Levi R × B.unipotentRadical R => B.leviAction R mu.1 mu.2) :=
  (((B.leviInParabolicContinuous R).continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.mul
      ((B.leviInParabolicContinuous R).continuous.comp continuous_fst).inv).subtype_mk _

variable [T2Space R]

omit [IsTopologicalRing R] in
private theorem isClosed_triangularSubgroup {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder α] (b : ι → α) :
    IsClosed (triangularSubgroup R b : Set (Matrix.GeneralLinearGroup ι R)) :=
  isClosed_setOfPred_blockTriangular.preimage
    (show Continuous (fun g : Matrix.GeneralLinearGroup ι R => g.val) from Units.continuous_val)

omit [IsTopologicalRing R] in
/-- The standard parabolic is closed in the actual general linear group. -/
theorem isClosed_parabolic : IsClosed (B.parabolic R : Set (Langlands.GeneralLinear n R)) :=
  (isClosed_triangularSubgroup R (Sigma.fst : B.Index → Fin B.length)).preimage
    (reindexContinuous (R := R) B.indexEquiv).symm.continuous

omit [IsTopologicalRing R] in
/-- The opposite parabolic is also closed. -/
theorem isClosed_oppositeParabolic :
    IsClosed (B.oppositeParabolic R : Set (Langlands.GeneralLinear n R)) :=
  (isClosed_triangularSubgroup R (fun a : B.Index => OrderDual.toDual a.1)).preimage
    (reindexContinuous (R := R) B.indexEquiv).symm.continuous

/-- The unipotent radical is closed in the parabolic, as a continuous kernel. -/
theorem isClosed_unipotentRadical :
    IsClosed (B.unipotentRadical R : Set (B.parabolic R)) :=
  isClosed_singleton.preimage (B.leviProjectionContinuous R).continuous

/-- The radical is also closed as a matrix subgroup of the full group. -/
theorem isClosed_unipotentSubgroup :
    IsClosed (B.unipotentSubgroup R : Set (Langlands.GeneralLinear n R)) :=
  (B.isClosed_parabolic R).isClosedMap_subtype_val _ (B.isClosed_unipotentRadical R)

omit [IsTopologicalRing R] in
/-- Local compactness transfers to the standard parabolic by its closed inclusion. -/
theorem parabolicLocallyCompactSpace [LocallyCompactSpace (Langlands.GeneralLinear n R)] :
    LocallyCompactSpace (B.parabolic R) :=
  (B.isClosed_parabolic R).locallyCompactSpace

omit [IsTopologicalRing R] in
/-- The opposite parabolic is locally compact whenever the ambient group is. -/
theorem oppositeParabolicLocallyCompactSpace
    [LocallyCompactSpace (Langlands.GeneralLinear n R)] :
    LocallyCompactSpace (B.oppositeParabolic R) :=
  (B.isClosed_oppositeParabolic R).locallyCompactSpace

/-- Local compactness transfers further to the unipotent radical. -/
theorem unipotentRadicalLocallyCompactSpace [LocallyCompactSpace (Langlands.GeneralLinear n R)] :
    LocallyCompactSpace (B.unipotentRadical R) := by
  have := B.parabolicLocallyCompactSpace R
  exact (B.isClosed_unipotentRadical R).locallyCompactSpace

end Topology

end BlockShape
end Langlands.GeneralLinear
