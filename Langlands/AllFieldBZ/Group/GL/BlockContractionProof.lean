import Langlands.AllFieldBZ.Group.GL.BlockContractionStatement
import Langlands.Group.GL.BlockContractionProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-!
# All-field port of `Langlands.Group.GL.BlockContractionProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockContractionProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped Topology
open scoped NNReal
open scoped Matrix.Norms.Elementwise
open Filter
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

theorem _root_.Langlands.GeneralLinear.BlockShape.strictPowersEventuallyDeep_allFieldBZ : B.StrictPowersEventuallyDeep_allFieldBZ T := by
  intro a ha ε hε
  apply eventually_atTop.mp
  apply (eventually_all).mpr
  intro i
  apply (eventually_all).mpr
  intro j
  by_cases hij : i < j
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (NNReal.coe_nonneg (B.blockScalarRatio_allFieldBZ T i j a : ℝ≥0)) (ha i j hij)).eventually
        (gt_mem_nhds hε)
    filter_upwards [h] with s hs _
    change (((B.blockScalarRatio_allFieldBZ T i j (a ^ s) : ℝ≥0) : ℝ)) < ε
    simpa only [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] using hs
  · exact Eventually.of_forall (fun _ h => (hij h).elim)

theorem _root_.Langlands.GeneralLinear.BlockShape.deepChamberNonempty_allFieldBZ : B.DeepChamberNonempty_allFieldBZ T := by
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
  have ha : B.IsStrictlyContracting_allFieldBZ T a := by
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
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep_allFieldBZ T a ha ε hε
  exact ⟨fun i => a i ^ r, hr r le_rfl⟩

private theorem _root_.Langlands.GeneralLinear.BlockShape.norm_nhds_one {K : Type*} [NormedField K] (n : ℕ)
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

private theorem _root_.Langlands.GeneralLinear.BlockShape.compact_matrix_bound {K : Type*} [NormedField K] {n : ℕ}
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

private theorem _root_.Langlands.GeneralLinear.BlockShape.upper_conj_norm_bound {K : Type*} [NormedField K]
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

private theorem _root_.Langlands.GeneralLinear.BlockShape.lower_conj_norm_bound {K : Type*} [NormedField K]
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

/-- The contraction argument for a normed field `K` whose norm topology is a given
topology `τ`, with a ratio function `ν` whose small values are small in norm. -/
private theorem uniformCompactBlockContraction_of_norm {K : Type*} [inst : Field K]
    (N : NontriviallyNormedField K) (hNf : N.toField = inst)
    (τ : TopologicalSpace K)
    (hτ : @UniformSpace.toTopologicalSpace K
      (@PseudoMetricSpace.toUniformSpace K N.toPseudoMetricSpace) = τ)
    (ν : K → ℝ)
    (hν : ∀ U : Set K, (letI := τ; U ∈ 𝓝 (0 : K)) → ∃ ε : ℝ, 0 < ε ∧ ∀ x, ν x < ε → x ∈ U)
    (deep : ℝ → (Fin B.length → Kˣ) → Prop)
    (hdeep : ∀ ε a, deep ε a → ∀ i j, i < j → ν ((a i * (a j)⁻¹ : Kˣ) : K) < ε) :
    letI := τ
    ∀ Cplus Cminus : Set (GeneralLinear n K),
      IsCompact Cplus →
      Cplus ⊆ (B.unipotentSubgroup K : Set (GeneralLinear n K)) →
      IsCompact Cminus →
      Cminus ⊆ (B.oppositeUnipotentSubgroup K : Set (GeneralLinear n K)) →
      ∀ U : Set (GeneralLinear n K), U ∈ 𝓝 (1 : GeneralLinear n K) →
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          ∀ a : Fin B.length → Kˣ, deep ε a →
            (∀ x ∈ Cplus, B.blockScalar K a * x * (B.blockScalar K a)⁻¹ ∈ U) ∧
            (∀ y ∈ Cminus, (B.blockScalar K a)⁻¹ * y * B.blockScalar K a ∈ U) := by
  subst hNf
  subst hτ
  let := N
  intro Cplus Cminus hCp hNp hCm hNm U hU
  obtain ⟨δ, hδ, hδU⟩ := norm_nhds_one n U hU
  obtain ⟨M, hM, hbound⟩ := compact_matrix_bound (hCp.union hCm)
  let η := δ / M
  have hη : 0 < η := div_pos hδ hM
  have hηM : η * M = δ := div_mul_cancel₀ δ hM.ne'
  obtain ⟨ε₀, hε₀, hsub⟩ := hν {x : K | ‖x‖ < η} (by
    have hb : Metric.ball (0 : K) η ∈ 𝓝 (0 : K) := Metric.ball_mem_nhds _ hη
    simpa only [Metric.ball, dist_zero_right] using hb)
  refine ⟨min 1 ε₀, lt_min zero_lt_one hε₀, min_le_left _ _, ?_⟩
  intro a ha
  have hratio : ∀ i j, i < j → ‖((a i * (a j)⁻¹ : Kˣ) : K)‖ < η := fun i j hij =>
    hsub _ ((hdeep _ a ha i j hij).trans_le (min_le_right _ _))
  constructor
  · intro x hx
    have hb := hbound x (Set.mem_union_left _ hx)
    apply hδU
    · simpa only [hηM] using B.upper_conj_norm_bound a (hNp hx) hη hM hb.1 hratio
    · have hi := B.upper_conj_norm_bound a
        ((B.unipotentSubgroup K).inv_mem (hNp hx)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi
  · intro y hy
    have hb := hbound y (Set.mem_union_right _ hy)
    apply hδU
    · simpa only [hηM] using B.lower_conj_norm_bound a (hNm hy) hη hM hb.1 hratio
    · have hi := B.lower_conj_norm_bound a
        ((B.oppositeUnipotentSubgroup K).inv_mem (hNm hy)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi

theorem _root_.Langlands.GeneralLinear.BlockShape.uniformCompactBlockContraction_allFieldBZ :
    B.UniformCompactBlockContraction_allFieldBZ T := by
  -- MANUAL: the p-adic proof used the canonical norm and `|x| = ‖x‖ ^ d`; here a norm
  -- inducing the topology is built from the valuation, as in `GeneralLocalField.properNormedField`, and the
  -- ratio bound from `exists_normalizedAbs_lt_subset`.
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let : (Valued.v (R := F.Carrier) (Γ₀ := ValuativeRel.ValueGroupWithZero F.Carrier)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F.Carrier).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let N : NontriviallyNormedField F.Carrier :=
    Valued.toNontriviallyNormedField (L := F.Carrier) (Γ₀ := ValuativeRel.ValueGroupWithZero F.Carrier)
  exact uniformCompactBlockContraction_of_norm B N rfl T.topology rfl
    T.normalizedAbs (fun U hU => T.exists_normalizedAbs_lt_subset hU)
    (B.IsDeeplyContracting_allFieldBZ T) (fun ε a ha i j hij => ha i j hij)

/-- High powers of any strict scalar carry radical elements into any open subgroup's
corresponding radical intersections. No factorization or compactness of the subgroup is needed. -/
theorem _root_.Langlands.GeneralLinear.BlockShape.strictPowers_eventually_mem_iwahori_allFieldBZ :
    letI := T.topology
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (a : Fin B.length → F.Carrierˣ), B.IsStrictlyContracting_allFieldBZ T a →
      ∀ (x y : GeneralLinear n F.Carrier), x ∈ B.unipotentSubgroup F.Carrier →
        y ∈ B.oppositeUnipotentSubgroup F.Carrier →
        ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
          (B.blockScalar F.Carrier a) ^ s * x * ((B.blockScalar F.Carrier a) ^ s)⁻¹ ∈
            B.iwahoriUpper F.Carrier K.toSubgroup ∧
          ((B.blockScalar F.Carrier a) ^ s)⁻¹ * y * (B.blockScalar F.Carrier a) ^ s ∈
            B.iwahoriLower F.Carrier K.toSubgroup := by
  let := T.topology
  intro K a ha x y hx hy
  obtain ⟨ε, hε, _, hc⟩ := B.uniformCompactBlockContraction_allFieldBZ T
    {x} {y} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
    isCompact_singleton (Set.singleton_subset_iff.mpr hy)
    K (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep_allFieldBZ T a ha ε hε
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

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
