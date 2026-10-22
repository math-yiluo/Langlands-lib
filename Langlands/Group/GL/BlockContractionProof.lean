import Langlands.Group.GL.BlockContractionStatement
import Mathlib.Analysis.Matrix.Normed

noncomputable section
open scoped Topology NNReal Matrix.Norms.Elementwise
open Filter

namespace Langlands.GeneralLinear.BlockShape
universe uF
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem strictPowersEventuallyDeep : B.StrictPowersEventuallyDeep T := by
  intro a ha ε hε
  apply eventually_atTop.mp
  apply (eventually_all).mpr
  intro i
  apply (eventually_all).mpr
  intro j
  by_cases hij : i < j
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (NNReal.coe_nonneg (B.blockScalarRatio T i j a : ℝ≥0)) (ha i j hij)).eventually
        (gt_mem_nhds hε)
    filter_upwards [h] with s hs _
    change (((B.blockScalarRatio T i j (a ^ s) : ℝ≥0) : ℝ)) < ε
    simpa only [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] using hs
  · exact Eventually.of_forall (fun _ h => (hij h).elim)

theorem deepChamberNonempty : B.DeepChamberNonempty T := by
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    contradiction
  let t : F.Carrierˣ := Units.mk0 T.uniformizer hπ
  have ht : (((T.normalizedAbsUnits t : ℝ≥0) : ℝ)) < 1 := by
    change T.normalizedAbs T.uniformizer < 1
    rw [T.normalizedAbs_uniformizer, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
  let a : Fin B.length → F.Carrierˣ := fun i => t ^ (B.length - i.val)
  have ha : B.IsStrictlyContracting T a := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have he : B.length - i.val = (j.val - i.val) + (B.length - j.val) := by omega
    have hr : a i * (a j)⁻¹ = t ^ (j.val - i.val) := by
      dsimp [a]
      rw [he, pow_add, mul_inv_cancel_right]
    change (((T.normalizedAbsUnits (a i * (a j)⁻¹) : ℝ≥0) : ℝ)) < 1
    rw [hr, map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    exact (pow_le_pow_of_le_one (NNReal.coe_nonneg _) ht.le
      (show 1 ≤ j.val - i.val by omega)).trans_lt (by simpa using ht)
  intro ε hε
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  exact ⟨fun i => a i ^ r, hr r le_rfl⟩

private theorem norm_nhds_one {K : Type*} [NormedField K] (n : ℕ)
    (U : Set (GeneralLinear n K)) (hU : U ∈ 𝓝 (1 : GeneralLinear n K)) :
    ∃ δ > 0, ∀ g : GeneralLinear n K,
      ‖(g : Matrix (Fin n) (Fin n) K) - 1‖ < δ →
      ‖((g⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) - 1‖ < δ → g ∈ U := by
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ, hδ, fun g hg hgi => hVU (hδV ?_)⟩
  change max (dist (g : Matrix (Fin n) (Fin n) K) 1)
    (dist (MulOpposite.op ((g⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K))
      (MulOpposite.op 1)) < δ
  simpa only [dist_eq_norm, ← MulOpposite.op_sub, MulOpposite.norm_op, max_lt_iff] using And.intro hg hgi

private theorem compact_matrix_bound {K : Type*} [NormedField K] {n : ℕ}
    {C : Set (GeneralLinear n K)} (hC : IsCompact C) :
    ∃ M > 0, ∀ g ∈ C,
      ‖(g : Matrix (Fin n) (Fin n) K)‖ ≤ M ∧
      ‖((g⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K)‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := hC.exists_bound_of_continuousOn Units.continuous_val.continuousOn
  obtain ⟨M₂, hM₂⟩ := hC.exists_bound_of_continuousOn Units.continuous_coe_inv.continuousOn
  refine ⟨max 1 (max M₁ M₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro g hg
  exact ⟨(hM₁ g hg).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hM₂ g hg).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

private theorem upper_conj_norm_bound {K : Type*} [NormedField K]
    (a : Fin B.length → Kˣ) {g : GeneralLinear n K}
    (hg : g ∈ B.unipotentSubgroup K) {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hbound : ‖(g : Matrix (Fin n) (Fin n) K)‖ ≤ M)
    (ha : ∀ i j, i < j → ‖((a i * (a j)⁻¹ : Kˣ) : K)‖ < η) :
    ‖((B.blockScalar K a * g * (B.blockScalar K a)⁻¹ : GeneralLinear n K) :
      Matrix (Fin n) (Fin n) K) - 1‖ < η * M := by
  have hconj := (B.mem_unipotentSubgroup_iff K _).mp
    (B.blockScalar_conj_mem_unipotentSubgroup K a hg)
  apply (Matrix.norm_lt_iff (mul_pos hη hM)).mpr
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ‖(B.blockScalar K a * g * (B.blockScalar K a)⁻¹) (B.index i r) (B.index j s) -
    (1 : Matrix (Fin n) (Fin n) K) (B.index i r) (B.index j s)‖ < η * M
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hidx : B.index i r ≠ B.index j s := by
      intro h
      exact hij.ne (congrArg Sigma.fst (B.indexEquiv.injective h))
    rw [B.blockScalar_conj_apply, Matrix.one_apply_ne hidx, sub_zero, norm_mul]
    exact (mul_le_mul_of_nonneg_left
      ((Matrix.norm_entry_le_entrywise_sup_norm _).trans hbound) (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right (ha i j hij) hM)
  · rw [hconj.2]
    simp only [Matrix.one_apply, (B.index i).injective.eq_iff, sub_self, norm_zero]
    exact mul_pos hη hM
  · have hidx : B.index i r ≠ B.index j s := by
      intro h
      exact hji.ne' (congrArg Sigma.fst (B.indexEquiv.injective h))
    rw [(B.mem_parabolic_iff K _).mp hconj.1 i j r s hji,
      Matrix.one_apply_ne hidx, sub_self, norm_zero]
    exact mul_pos hη hM

private theorem lower_conj_norm_bound {K : Type*} [NormedField K]
    (a : Fin B.length → Kˣ) {g : GeneralLinear n K}
    (hg : g ∈ B.oppositeUnipotentSubgroup K) {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hbound : ‖(g : Matrix (Fin n) (Fin n) K)‖ ≤ M)
    (ha : ∀ i j, i < j → ‖((a i * (a j)⁻¹ : Kˣ) : K)‖ < η) :
    ‖(((B.blockScalar K a)⁻¹ * g * B.blockScalar K a : GeneralLinear n K) :
      Matrix (Fin n) (Fin n) K) - 1‖ < η * M := by
  have hconj := (B.mem_oppositeUnipotentSubgroup_iff K _).mp
    (B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup K a hg)
  apply (Matrix.norm_lt_iff (mul_pos hη hM)).mpr
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ‖((B.blockScalar K a)⁻¹ * g * B.blockScalar K a) (B.index i r) (B.index j s) -
    (1 : Matrix (Fin n) (Fin n) K) (B.index i r) (B.index j s)‖ < η * M
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hidx : B.index i r ≠ B.index j s := by
      intro h
      exact hij.ne (congrArg Sigma.fst (B.indexEquiv.injective h))
    rw [(B.mem_oppositeParabolic_iff K _).mp hconj.1 i j r s hij,
      Matrix.one_apply_ne hidx, sub_self, norm_zero]
    exact mul_pos hη hM
  · rw [hconj.2]
    simp only [Matrix.one_apply, (B.index i).injective.eq_iff, sub_self, norm_zero]
    exact mul_pos hη hM
  · have hidx : B.index i r ≠ B.index j s := by
      intro h
      exact hji.ne' (congrArg Sigma.fst (B.indexEquiv.injective h))
    rw [B.blockScalar_inv_conj_apply, Matrix.one_apply_ne hidx, sub_zero, norm_mul]
    have hratio : ‖(((a i)⁻¹ * a j : Kˣ) : K)‖ < η := by
      simpa only [mul_comm] using ha j i hji
    exact (mul_le_mul_of_nonneg_left
      ((Matrix.norm_entry_le_entrywise_sup_norm _).trans hbound) (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right hratio hM)

theorem uniformCompactBlockContraction : B.UniformCompactBlockContraction T := by
  unfold UniformCompactBlockContraction
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  intro Cplus Cminus hCp hNp hCm hNm U hU
  obtain ⟨δ, hδ, hδU⟩ := norm_nhds_one n U hU
  obtain ⟨M, hM, hbound⟩ := compact_matrix_bound (hCp.union hCm)
  let η := δ / M
  have hη : 0 < η := div_pos hδ hM
  have hηM : η * M = δ := div_mul_cancel₀ δ hM.ne'
  let d := Module.finrank (Padic p) F.Carrier
  have hd : d ≠ 0 := (PadicField.TopologicalData.extensionDegree_pos (F := F)).ne'
  refine ⟨min 1 (η ^ d), lt_min zero_lt_one (pow_pos hη _), min_le_left _ _, ?_⟩
  intro a ha
  have hratio : ∀ i j, i < j → ‖((a i * (a j)⁻¹ : F.Carrierˣ) : F.Carrier)‖ < η := by
    intro i j hij
    have h := (ha i j hij).trans_le (min_le_right _ _)
    change T.normalizedAbs ((a i * (a j)⁻¹ : F.Carrierˣ) : F.Carrier) < η ^ d at h
    rw [T.normalizedAbs_eq_canonicalNorm_pow_degree] at h
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hη.le hd).mp h
  constructor
  · intro x hx
    have hb := hbound x (Set.mem_union_left _ hx)
    apply hδU
    · simpa only [hηM] using B.upper_conj_norm_bound a (hNp hx) hη hM hb.1 hratio
    · have hi := B.upper_conj_norm_bound a
        ((B.unipotentSubgroup F.Carrier).inv_mem (hNp hx)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi
  · intro y hy
    have hb := hbound y (Set.mem_union_right _ hy)
    apply hδU
    · simpa only [hηM] using B.lower_conj_norm_bound a (hNm hy) hη hM hb.1 hratio
    · have hi := B.lower_conj_norm_bound a
        ((B.oppositeUnipotentSubgroup F.Carrier).inv_mem (hNm hy)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi

/-- The exact published uniform block-contraction proposition. -/
theorem blockContraction : BlockContractionStatement.{uF} := by
  intro p hp F T n B
  exact ⟨B.deepChamberNonempty T, B.uniformCompactBlockContraction T,
    B.strictPowersEventuallyDeep T⟩

/-- High powers of any strict scalar carry radical elements into any open subgroup's
corresponding radical intersections. No factorization or compactness of the subgroup is needed. -/
theorem strictPowers_eventually_mem_iwahori :
    letI := T.topology
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (a : Fin B.length → F.Carrierˣ), B.IsStrictlyContracting T a →
      ∀ (x y : GeneralLinear n F.Carrier), x ∈ B.unipotentSubgroup F.Carrier →
        y ∈ B.oppositeUnipotentSubgroup F.Carrier →
        ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
          (B.blockScalar F.Carrier a) ^ s * x * ((B.blockScalar F.Carrier a) ^ s)⁻¹ ∈
            B.iwahoriUpper F.Carrier K.toSubgroup ∧
          ((B.blockScalar F.Carrier a) ^ s)⁻¹ * y * (B.blockScalar F.Carrier a) ^ s ∈
            B.iwahoriLower F.Carrier K.toSubgroup := by
  let := T.topology
  intro K a ha x y hx hy
  obtain ⟨ε, hε, _, hc⟩ := B.uniformCompactBlockContraction T
    {x} {y} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
    isCompact_singleton (Set.singleton_subset_iff.mpr hy)
    K (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  refine ⟨r, fun s hs => ?_⟩
  have hc' := hc (fun i => a i ^ s) (hr s hs)
  have hpow : B.blockScalar F.Carrier (fun i => a i ^ s) =
      (B.blockScalar F.Carrier a) ^ s := map_pow (B.blockScalar F.Carrier) a s
  constructor
  · rw [← hpow]
    exact ⟨hc'.1 x (Set.mem_singleton x),
      B.blockScalar_conj_mem_unipotentSubgroup F.Carrier _ hx⟩
  · rw [← hpow]
    exact ⟨hc'.2 y (Set.mem_singleton y),
      B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F.Carrier _ hy⟩

end Langlands.GeneralLinear.BlockShape
