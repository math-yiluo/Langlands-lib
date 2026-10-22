import Langlands.Group.GL.Blocks

/-!
# Levi decomposition of the opposite block parabolic
-/

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

private theorem lower_diagonalBlock_one (i : Fin B.length) :
    B.diagonalBlock R 1 i = 1 := by
  ext a b
  simp [diagonalBlock, Matrix.one_apply]

private theorem lower_diagonalBlock_mul
    {A C : Matrix B.Index B.Index R}
    (hA : A.BlockTriangular (fun a : B.Index => OrderDual.toDual a.1))
    (hC : C.BlockTriangular (fun a : B.Index => OrderDual.toDual a.1))
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
  · rw [hC (i := ⟨j, k⟩) (j := ⟨i, b⟩) hji, mul_zero]
  · rw [hA (i := ⟨i, a⟩) (j := ⟨j, k⟩) hij, zero_mul]

private def oppositeDiagonalBlock (g : B.oppositeParabolic R) (i : Fin B.length) :
    Matrix (Fin (B.size i)) (Fin (B.size i)) R :=
  B.diagonalBlock R ((reindex (R := R) B.indexEquiv).symm g.val).val i

private theorem oppositeDiagonalBlock_one (i : Fin B.length) :
    B.oppositeDiagonalBlock R 1 i = 1 := by
  change B.diagonalBlock R ((reindex (R := R) B.indexEquiv).symm 1).val i = 1
  rw [map_one]
  exact B.lower_diagonalBlock_one R i

private theorem oppositeDiagonalBlock_mul (g h : B.oppositeParabolic R)
    (i : Fin B.length) :
    B.oppositeDiagonalBlock R (g * h) i =
      B.oppositeDiagonalBlock R g i * B.oppositeDiagonalBlock R h i := by
  change B.diagonalBlock R
    ((reindex (R := R) B.indexEquiv).symm (g.val * h.val)).val i = _
  rw [map_mul]
  exact B.lower_diagonalBlock_mul R g.property h.property i

/-- Extract the actual invertible diagonal blocks of the lower block parabolic. -/
def oppositeLeviProjection : B.oppositeParabolic R →* B.Levi R where
  toFun g i :=
    { val := B.oppositeDiagonalBlock R g i
      inv := B.oppositeDiagonalBlock R g⁻¹ i
      val_inv := by
        rw [← B.oppositeDiagonalBlock_mul R, mul_inv_cancel]
        exact B.oppositeDiagonalBlock_one R i
      inv_val := by
        rw [← B.oppositeDiagonalBlock_mul R, inv_mul_cancel]
        exact B.oppositeDiagonalBlock_one R i }
  map_one' := by
    funext i
    exact Units.ext (B.oppositeDiagonalBlock_one R i)
  map_mul' g h := by
    funext i
    exact Units.ext (B.oppositeDiagonalBlock_mul R g h i)

/-- The opposite projection reads the same standard diagonal coordinates as the upper one. -/
@[simp] theorem oppositeLeviProjection_apply (g : B.oppositeParabolic R)
    (i : Fin B.length) (a b : Fin (B.size i)) :
    B.oppositeLeviProjection R g i a b = g.val (B.index i a) (B.index i b) := rfl

/-- The common block diagonal Levi embedding, now valued in the opposite parabolic. -/
def oppositeLeviInParabolic : B.Levi R →* B.oppositeParabolic R :=
  (B.leviEmbedding R).codRestrict _ fun m =>
    (B.mem_oppositeParabolic_iff R _).mpr (by
      intro i j a b hij
      exact B.leviEmbedding_apply_ne R m a b (ne_of_lt hij))

@[simp] theorem oppositeLeviInParabolic_val (m : B.Levi R) :
    (B.oppositeLeviInParabolic R m).val = B.leviEmbedding R m := rfl

/-- Both parabolics use exactly the same Levi matrices in the ambient group. -/
theorem commonLeviEmbedding (m : B.Levi R) :
    (B.oppositeLeviInParabolic R m).val = (B.leviInParabolic R m).val := rfl

@[simp] theorem oppositeLeviProjection_section (m : B.Levi R) :
    B.oppositeLeviProjection R (B.oppositeLeviInParabolic R m) = m := by
  funext i
  apply Units.ext
  ext a b
  exact B.leviEmbedding_apply_same R m i a b

/-- The opposite unipotent radical is the kernel of the actual lower-block projection. -/
def oppositeUnipotentRadical : Subgroup (B.oppositeParabolic R) :=
  (B.oppositeLeviProjection R).ker

instance oppositeUnipotentRadicalNormal : (B.oppositeUnipotentRadical R).Normal :=
  inferInstanceAs (B.oppositeLeviProjection R).ker.Normal

/-- Include the opposite radical as a subgroup of the ambient matrix group. -/
def oppositeUnipotentSubgroup : Subgroup (Langlands.GeneralLinear n R) :=
  (B.oppositeUnipotentRadical R).map (B.oppositeParabolic R).subtype

/-- Conjugation by the common Levi on the opposite unipotent radical. -/
def oppositeLeviAction : B.Levi R →* MulAut (B.oppositeUnipotentRadical R) :=
  MulAut.conjNormal.comp (B.oppositeLeviInParabolic R)

/-- Remove the lower parabolic's diagonal part on the right. -/
def oppositeUnipotentPart (g : B.oppositeParabolic R) : B.oppositeUnipotentRadical R :=
  ⟨g * (B.oppositeLeviInParabolic R (B.oppositeLeviProjection R g))⁻¹, by
    change B.oppositeLeviProjection R
      (g * (B.oppositeLeviInParabolic R (B.oppositeLeviProjection R g))⁻¹) = 1
    simp⟩

/-- The constructed unique factorization `g = u * Levi(m)` for the opposite parabolic. -/
def oppositeDecomposition :
    B.oppositeParabolic R ≃ B.oppositeUnipotentRadical R × B.Levi R where
  toFun g := (B.oppositeUnipotentPart R g, B.oppositeLeviProjection R g)
  invFun um := um.1.val * B.oppositeLeviInParabolic R um.2
  left_inv g := inv_mul_cancel_right _ _
  right_inv um := by
    rcases um with ⟨u, m⟩
    have hu : B.oppositeLeviProjection R u.val = 1 := u.property
    have hp : B.oppositeLeviProjection R (u.val * B.oppositeLeviInParabolic R m) = m := by
      simp [hu]
    apply Prod.ext
    · apply Subtype.ext
      change u.val * B.oppositeLeviInParabolic R m *
        (B.oppositeLeviInParabolic R
          (B.oppositeLeviProjection R (u.val * B.oppositeLeviInParabolic R m)))⁻¹ = u.val
      rw [hp, mul_inv_cancel_right]
    · exact hp

/-- The opposite radical has identity diagonal blocks. -/
theorem mem_oppositeUnipotentRadical_iff (g : B.oppositeParabolic R) :
    g ∈ B.oppositeUnipotentRadical R ↔
      ∀ (i : Fin B.length) (a b : Fin (B.size i)),
        g.val (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  change B.oppositeLeviProjection R g = 1 ↔ _
  constructor
  · intro hg i a b
    have h := congrArg (fun m : B.Levi R => m i a b) hg
    simpa only [oppositeLeviProjection_apply, Pi.one_apply,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] using h
  · intro hg
    funext i
    apply Units.ext
    ext a b
    exact hg i a b

/-- The ambient opposite radical is precisely lower block triangular with identity blocks. -/
theorem mem_oppositeUnipotentSubgroup_iff (g : Langlands.GeneralLinear n R) :
    g ∈ B.oppositeUnipotentSubgroup R ↔
      g ∈ B.oppositeParabolic R ∧
        ∀ (i : Fin B.length) (a b : Fin (B.size i)),
          g (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, (B.mem_oppositeUnipotentRadical_iff R h).mp hh⟩
  · rintro ⟨hg, hd⟩
    exact ⟨⟨g, hg⟩, (B.mem_oppositeUnipotentRadical_iff R ⟨g, hg⟩).mpr hd, rfl⟩

/-- Common Levi conjugation preserves the upper ambient radical. -/
theorem levi_conj_mem_unipotentSubgroup (m : B.Levi R)
    {g : Langlands.GeneralLinear n R} (hg : g ∈ B.unipotentSubgroup R) :
    B.leviEmbedding R m * g * (B.leviEmbedding R m)⁻¹ ∈ B.unipotentSubgroup R := by
  rcases hg with ⟨u, hu, rfl⟩
  refine ⟨B.leviInParabolic R m * u * (B.leviInParabolic R m)⁻¹, ?_, rfl⟩
  have hu' : B.leviProjection R u = 1 := hu
  change B.leviProjection R
    (B.leviInParabolic R m * u * (B.leviInParabolic R m)⁻¹) = 1
  simp [hu']

/-- Common Levi conjugation preserves the lower ambient radical. -/
theorem levi_conj_mem_oppositeUnipotentSubgroup (m : B.Levi R)
    {g : Langlands.GeneralLinear n R} (hg : g ∈ B.oppositeUnipotentSubgroup R) :
    B.leviEmbedding R m * g * (B.leviEmbedding R m)⁻¹ ∈
      B.oppositeUnipotentSubgroup R := by
  rcases hg with ⟨u, hu, rfl⟩
  refine ⟨B.oppositeLeviInParabolic R m * u *
    (B.oppositeLeviInParabolic R m)⁻¹, ?_, rfl⟩
  have hu' : B.oppositeLeviProjection R u = 1 := hu
  change B.oppositeLeviProjection R
    (B.oppositeLeviInParabolic R m * u * (B.oppositeLeviInParabolic R m)⁻¹) = 1
  simp [hu']

/-- The actual common Levi subgroup normalizes the upper radical in the full group. -/
theorem leviSubgroup_le_normalizer_unipotentSubgroup :
    B.leviSubgroup R ≤ Subgroup.normalizer (B.unipotentSubgroup R) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨m, rfl⟩ g hg
  exact B.levi_conj_mem_unipotentSubgroup R m hg

/-- The same actual Levi subgroup normalizes the opposite radical in the full group. -/
theorem leviSubgroup_le_normalizer_oppositeUnipotentSubgroup :
    B.leviSubgroup R ≤ Subgroup.normalizer (B.oppositeUnipotentSubgroup R) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨m, rfl⟩ g hg
  exact B.levi_conj_mem_oppositeUnipotentSubgroup R m hg

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

private theorem continuous_oppositeLeviProjection : Continuous (B.oppositeLeviProjection R) := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g : B.oppositeParabolic R =>
      B.oppositeDiagonalBlock R g i)
    apply continuous_matrix
    intro a b
    exact (continuous_apply (B.index i b)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_subtype_val (B.index i a))
  · change Continuous (fun g : B.oppositeParabolic R =>
      B.oppositeDiagonalBlock R g⁻¹ i)
    apply continuous_matrix
    intro a b
    exact (continuous_apply (B.index i b)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _
        (continuous_inv.comp continuous_subtype_val) (B.index i a))

/-- The diagonal-block projection of the opposite parabolic is continuous. -/
def oppositeLeviProjectionContinuous :
    ContinuousMonoidHom (B.oppositeParabolic R) (B.Levi R) where
  toMonoidHom := B.oppositeLeviProjection R
  continuous_toFun := B.continuous_oppositeLeviProjection R

/-- The common block diagonal section is continuous into the opposite parabolic. -/
def oppositeLeviInParabolicContinuous :
    ContinuousMonoidHom (B.Levi R) (B.oppositeParabolic R) where
  toMonoidHom := B.oppositeLeviInParabolic R
  continuous_toFun := (B.leviEmbeddingContinuous R).continuous.subtype_mk _

/-- The proved lower `u*m` factorization respects all inherited topologies. -/
def oppositeDecompositionHomeomorph :
    B.oppositeParabolic R ≃ₜ B.oppositeUnipotentRadical R × B.Levi R where
  toEquiv := B.oppositeDecomposition R
  continuous_toFun :=
    ((continuous_id.mul ((B.oppositeLeviInParabolicContinuous R).continuous.comp
      (B.oppositeLeviProjectionContinuous R).continuous).inv).subtype_mk _).prodMk
        (B.oppositeLeviProjectionContinuous R).continuous
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((B.oppositeLeviInParabolicContinuous R).continuous.comp continuous_snd)

/-- The common Levi action on the opposite radical is jointly continuous. -/
theorem continuous_oppositeLeviAction :
    Continuous (fun mu : B.Levi R × B.oppositeUnipotentRadical R =>
      B.oppositeLeviAction R mu.1 mu.2) :=
  (((B.oppositeLeviInParabolicContinuous R).continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.mul
      ((B.oppositeLeviInParabolicContinuous R).continuous.comp continuous_fst).inv).subtype_mk _

variable [T2Space R]

/-- The opposite radical is closed in the opposite parabolic as a continuous kernel. -/
theorem isClosed_oppositeUnipotentRadical :
    IsClosed (B.oppositeUnipotentRadical R : Set (B.oppositeParabolic R)) :=
  isClosed_singleton.preimage (B.oppositeLeviProjectionContinuous R).continuous

/-- The opposite radical is also closed in the ambient general linear group. -/
theorem isClosed_oppositeUnipotentSubgroup :
    IsClosed (B.oppositeUnipotentSubgroup R : Set (Langlands.GeneralLinear n R)) :=
  (B.isClosed_oppositeParabolic R).isClosedMap_subtype_val _
    (B.isClosed_oppositeUnipotentRadical R)

/-- Closedness transfers local compactness from the ambient group to the opposite radical. -/
theorem oppositeUnipotentRadicalLocallyCompactSpace
    [LocallyCompactSpace (Langlands.GeneralLinear n R)] :
    LocallyCompactSpace (B.oppositeUnipotentRadical R) := by
  have := B.oppositeParabolicLocallyCompactSpace R
  exact (B.isClosed_oppositeUnipotentRadical R).locallyCompactSpace

end Topology

end Langlands.GeneralLinear.BlockShape
