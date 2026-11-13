import Langlands.Group.GL.BlockContractionProof
import Langlands.AllField.Group.GL.BlockContractionStatement
noncomputable section
open scoped Topology NNReal Matrix.Norms.Elementwise
open Filter

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding DeepChamberNonempty HasBlockIwahoriFactorization IsDeeplyContracting IsStrictlyContracting IsWeaklyContracting StrictPowersEventuallyDeep UniformCompactBlockContraction blockScalarRatio blockScalarRatio_apply deepChamberNonempty isWeaklyContracting_one strictPowersEventuallyDeep strictPowers_eventually_mem_iwahori uniformCompactBlockContraction
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
universe uF
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {F : Type uF} [Field F] (T : LocalFieldData F)

theorem strictPowersEventuallyDeep : (Langlands.AllField.GeneralLinear.BlockShape.StrictPowersEventuallyDeep B) T := by
  intro a ha ε hε
  apply eventually_atTop.mp
  apply (eventually_all).mpr
  intro i
  apply (eventually_all).mpr
  intro j
  by_cases hij : i < j
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (NNReal.coe_nonneg ((Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j a : ℝ≥0)) (ha i j hij)).eventually
        (gt_mem_nhds hε)
    filter_upwards [h] with s hs _
    change ((((Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio B) T i j (a ^ s) : ℝ≥0) : ℝ)) < ε
    simpa only [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] using hs
  · exact Eventually.of_forall (fun _ h => (hij h).elim)

theorem deepChamberNonempty : (Langlands.AllField.GeneralLinear.BlockShape.DeepChamberNonempty B) T := by
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    contradiction
  let t : Fˣ := Units.mk0 T.uniformizer hπ
  have ht : (((T.normalizedAbsUnits t : ℝ≥0) : ℝ)) < 1 := by
    change T.normalizedAbs T.uniformizer < 1
    rw [T.normalizedAbs_uniformizer, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
  let a : Fin B.length → Fˣ := fun i => t ^ (B.length - i.val)
  have ha : (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a := by
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
  obtain ⟨r, hr⟩ := (Langlands.AllField.GeneralLinear.BlockShape.strictPowersEventuallyDeep B) T a ha ε hε
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

/-- The normed-field structure on `F` whose norm is the normalized absolute value
`T.normalizedAbs` and whose distance is `T.normalizedAbs (x - y)`. -/
@[instance_reducible]
private noncomputable def absNormedField (T : LocalFieldData F) : NormedField F :=
  { (inferInstance : Field F) with
    norm := T.normalizedAbs
    dist := fun x y => T.normalizedAbs (x - y)
    dist_self := fun x => by simp [T.normalizedAbs_zero]
    dist_comm := fun x y => by
      rw [← neg_sub, T.normalizedAbs_neg]
    dist_triangle := fun x y z => by
      rw [← sub_add_sub_cancel x y z]
      exact (T.normalizedAbs_add_le_max _ _).trans
        (max_le_add_of_nonneg (T.normalizedAbs_nonneg _) (T.normalizedAbs_nonneg _))
    eq_of_dist_eq_zero := fun {x y} h =>
      eq_of_sub_eq_zero ((T.normalizedAbs_eq_zero_iff _).mp h)
    dist_eq := fun x y => by
      change T.normalizedAbs (x - y) = T.normalizedAbs (-x + y)
      rw [neg_add_eq_sub, ← T.normalizedAbs_neg (y - x), neg_sub]
    norm_mul := T.normalizedAbs_mul }

/-- The supplied topology is the metric topology of `absNormedField`. -/
private theorem topology_eq_absNormTopology (T : LocalFieldData F) :
    T.topology = (letI := absNormedField T
      inferInstance : TopologicalSpace F) := by
  let := absNormedField T
  refine TopologicalSpace.ext_nhds fun a => ?_
  exact (T.hasBasis_nhds_normalizedAbs a).eq_of_same_basis Metric.nhds_basis_ball

theorem uniformCompactBlockContraction : (Langlands.AllField.GeneralLinear.BlockShape.UniformCompactBlockContraction B) T := by
  unfold UniformCompactBlockContraction
  rw [topology_eq_absNormTopology T]
  let := absNormedField T
  intro Cplus Cminus hCp hNp hCm hNm U hU
  obtain ⟨δ, hδ, hδU⟩ := norm_nhds_one n U hU
  obtain ⟨M, hM, hbound⟩ := compact_matrix_bound (hCp.union hCm)
  let η := δ / M
  have hη : 0 < η := div_pos hδ hM
  have hηM : η * M = δ := div_mul_cancel₀ δ hM.ne'
  refine ⟨min 1 η, lt_min zero_lt_one hη, min_le_left _ _, ?_⟩
  intro a ha
  have hratio : ∀ i j, i < j → ‖((a i * (a j)⁻¹ : Fˣ) : F)‖ < η := by
    intro i j hij
    exact (ha i j hij).trans_le (min_le_right _ _)
  constructor
  · intro x hx
    have hb := hbound x (Set.mem_union_left _ hx)
    apply hδU
    · simpa only [hηM] using upper_conj_norm_bound B a (hNp hx) hη hM hb.1 hratio
    · have hi := upper_conj_norm_bound B a
        ((B.unipotentSubgroup F).inv_mem (hNp hx)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi
  · intro y hy
    have hb := hbound y (Set.mem_union_right _ hy)
    apply hδU
    · simpa only [hηM] using lower_conj_norm_bound B a (hNm hy) hη hM hb.1 hratio
    · have hi := lower_conj_norm_bound B a
        ((B.oppositeUnipotentSubgroup F).inv_mem (hNm hy)) hη hM hb.2 hratio
      simpa only [mul_inv_rev, inv_inv, mul_assoc, hηM] using hi

/-- High powers of any strict scalar carry radical elements into any open subgroup's
corresponding radical intersections. No factorization or compactness of the subgroup is needed. -/
theorem strictPowers_eventually_mem_iwahori :
    letI := T.topology
    ∀ (K : OpenSubgroup (GeneralLinear n F))
      (a : Fin B.length → Fˣ), (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a →
      ∀ (x y : GeneralLinear n F), x ∈ B.unipotentSubgroup F →
        y ∈ B.oppositeUnipotentSubgroup F →
        ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
          (B.blockScalar F a) ^ s * x * ((B.blockScalar F a) ^ s)⁻¹ ∈
            B.iwahoriUpper F K.toSubgroup ∧
          ((B.blockScalar F a) ^ s)⁻¹ * y * (B.blockScalar F a) ^ s ∈
            B.iwahoriLower F K.toSubgroup := by
  let := T.topology
  intro K a ha x y hx hy
  obtain ⟨ε, hε, _, hc⟩ := (Langlands.AllField.GeneralLinear.BlockShape.uniformCompactBlockContraction B) T
    {x} {y} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
    isCompact_singleton (Set.singleton_subset_iff.mpr hy)
    K (K.isOpen.mem_nhds K.one_mem)
  obtain ⟨r, hr⟩ := (Langlands.AllField.GeneralLinear.BlockShape.strictPowersEventuallyDeep B) T a ha ε hε
  refine ⟨r, fun s hs => ?_⟩
  have hc' := hc (fun i => a i ^ s) (hr s hs)
  have hpow : B.blockScalar F (fun i => a i ^ s) =
      (B.blockScalar F a) ^ s := map_pow (B.blockScalar F) a s
  constructor
  · rw [← hpow]
    exact ⟨hc'.1 x (Set.mem_singleton x),
      B.blockScalar_conj_mem_unipotentSubgroup F _ hx⟩
  · rw [← hpow]
    exact ⟨hc'.2 y (Set.mem_singleton y),
      B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F _ hy⟩

end Langlands.AllField.GeneralLinear.BlockShape
