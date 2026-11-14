import Langlands.Analysis.Local.CompactFactorizationHaar

/-!
# Haar measure of saturated sets when an open subgroup factors as `H₁ = Q K`

Let `Q` be a closed subgroup, `K` a compact subgroup and `H₁ ⊇ K` an open subgroup of a second
countable locally compact group `G`, with `H₁ ⊆ Q K`. For a right `K`-saturated measurable set
`A`, the Haar measure of `A ∩ Q H₁` is a fixed multiple of the Haar measure of `A ∩ Q`.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped NNReal ENNReal Pointwise

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The inclusion of `Q ⊓ H₁`, viewed as a subgroup of `H₁`, into `Q`. -/
def subgroupOfInclusion (Q H₁ : Subgroup G) : Q.subgroupOf H₁ →* Q where
  toFun x := ⟨((x : H₁) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
@[simp] theorem coe_subgroupOfInclusion (Q H₁ : Subgroup G) (x : Q.subgroupOf H₁) :
    ((subgroupOfInclusion Q H₁ x : Q) : G) = ((x : H₁) : G) := rfl

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- For an open `H₁`, the inclusion `Q ⊓ H₁ → Q` is an open embedding. -/
theorem isOpenEmbedding_subgroupOfInclusion (Q H₁ : Subgroup G) (hH₁ : IsOpen (H₁ : Set G)) :
    IsOpenEmbedding (subgroupOfInclusion Q H₁) := by
  have hcomp : IsEmbedding ((Subtype.val : Q → G) ∘ subgroupOfInclusion Q H₁) := by
    have : ((Subtype.val : Q → G) ∘ subgroupOfInclusion Q H₁) =
        (Subtype.val : H₁ → G) ∘ (Subtype.val : Q.subgroupOf H₁ → H₁) := rfl
    rw [this]
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hemb : IsEmbedding (subgroupOfInclusion Q H₁) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp hcomp
  refine ⟨hemb, ?_⟩
  have hrange : range (subgroupOfInclusion Q H₁) = (Subtype.val : Q → G) ⁻¹' (H₁ : Set G) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact (x : H₁).2
    · intro hq
      exact ⟨⟨⟨q, hq⟩, Subgroup.mem_subgroupOf.mpr q.2⟩, rfl⟩
  rw [hrange]
  exact hH₁.preimage continuous_subtype_val

/-- **Haar measure of a right `K`-saturated set, open-subgroup version.** Let `Q` be a closed
subgroup, `K` a compact subgroup and `H₁` an open subgroup containing `K` with every element of
`H₁` a product `q k`, `q ∈ Q`, `k ∈ K`. Then there is a constant `c` such that every measurable
right `K`-saturated set `A` satisfies `μ (A ∩ Q H₁) = c μ_Q (A ∩ Q)`. -/
theorem exists_measure_inter_mul_eq_of_isOpen (μ : Measure G) [IsHaarMeasure μ]
    (Q : Subgroup G) (hQ : IsClosed (Q : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (H₁ : Subgroup G) (hH₁ : IsOpen (H₁ : Set G)) (hKH : K ≤ H₁)
    (hQK : ∀ g ∈ H₁, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (μQ : Measure Q) [IsHaarMeasure μQ] :
    ∃ c : ℝ≥0, ∀ A : Set G, MeasurableSet A → (∀ a ∈ A, ∀ k ∈ K, a * k ∈ A) →
      μ (A ∩ ((Q : Set G) * (H₁ : Set G))) = c * μQ ((Subtype.val : Q → G) ⁻¹' A) := by
  classical
  have hH₁c : IsClosed (H₁ : Set G) := H₁.isClosed_of_isOpen hH₁
  have : LocallyCompactSpace H₁ := hH₁.locallyCompactSpace
  have : SecondCountableTopology H₁ :=
    TopologicalSpace.Subtype.secondCountableTopology (H₁ : Set G)
  -- the Haar measure of `H₁`, restricted from `G`
  have hemb₁ : IsOpenEmbedding H₁.subtype := hH₁.isOpenEmbedding_subtypeVal
  let μ₁ : Measure H₁ := μ.comap H₁.subtype
  have : IsHaarMeasure μ₁ := IsHaarMeasure.comap (mH := inferInstance) μ hemb₁
  -- the factorization inside `H₁`
  let Q₁ : Subgroup H₁ := Q.subgroupOf H₁
  have hQ₁ : IsClosed (Q₁ : Set H₁) := hQ.preimage continuous_subtype_val
  let K₁ : Subgroup H₁ := K.subgroupOf H₁
  have hK₁ : IsCompact (K₁ : Set H₁) := by
    rw [Subgroup.coe_subgroupOf]
    exact hH₁c.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQK₁ : ∀ g : H₁, ∃ q ∈ Q₁, ∃ k ∈ K₁, g = q * k := by
    intro g
    obtain ⟨q, hq, k, hk, hgqk⟩ := hQK g g.2
    have hqH : q ∈ H₁ := by
      have hq' : q = (g : G) * k⁻¹ := by rw [hgqk]; group
      rw [hq']
      exact H₁.mul_mem g.2 (H₁.inv_mem (hKH hk))
    exact ⟨⟨q, hqH⟩, Subgroup.mem_subgroupOf.mpr hq, ⟨k, hKH hk⟩,
      Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hgqk⟩
  -- the Haar measure of `Q₁`, restricted from `Q`
  let ι := subgroupOfInclusion Q H₁
  have hι : IsOpenEmbedding ι := isOpenEmbedding_subgroupOfInclusion Q H₁ hH₁
  let μQ₁ : Measure Q₁ := μQ.comap ι
  have : IsHaarMeasure μQ₁ := IsHaarMeasure.comap (mH := inferInstance) μQ hι
  obtain ⟨c, -, hc⟩ := exists_pos_measure_eq_of_mul_mem μ₁ Q₁ hQ₁ K₁ hK₁ hQK₁ μQ₁
  refine ⟨c, fun A hA hAK => ?_⟩
  -- the cosets of `O = Q ⊓ H₁` in `Q`
  let O : Subgroup Q := H₁.subgroupOf Q
  have hO : IsOpen (O : Set Q) := hH₁.preimage continuous_subtype_val
  have : DiscreteTopology (Q ⧸ O) := QuotientGroup.discreteTopology hO
  have : Countable (Q ⧸ O) := by
    have : TopologicalSpace.SeparableSpace (Q ⧸ O) :=
      inferInstanceAs (TopologicalSpace.SeparableSpace (Quotient (QuotientGroup.leftRel O)))
    exact TopologicalSpace.separableSpace_iff_countable.mp this
  let r : Q ⧸ O → Q := fun α => α.out
  have hr : ∀ α, (QuotientGroup.mk (r α) : Q ⧸ O) = α := fun α => QuotientGroup.out_eq' α
  -- coset membership in `Q`
  have hmemQ : ∀ (α : Q ⧸ O) (q : Q), q ∈ (r α) • (O : Set Q) ↔
      (QuotientGroup.mk q : Q ⧸ O) = α := by
    intro α q
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    conv_rhs => rw [← hr α]
    rw [eq_comm, QuotientGroup.eq]
    exact Iff.rfl
  -- coset membership in `G`
  have hmemG : ∀ (α : Q ⧸ O) (x : G), x ∈ ((r α : Q) : G) • (H₁ : Set G) →
      ∀ q : Q, ((q : G)⁻¹ * x ∈ H₁ ↔ (QuotientGroup.mk q : Q ⧸ O) = α) := by
    intro α x hx q
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    rw [← hr α, QuotientGroup.eq]
    change _ ↔ ((q⁻¹ * r α : Q) : G) ∈ H₁
    constructor
    · intro h
      have := H₁.mul_mem h (H₁.inv_mem hx)
      simpa [mul_assoc] using this
    · intro h
      have := H₁.mul_mem h hx
      simpa [mul_assoc] using this
  -- the pieces in `G`
  let P : Q ⧸ O → Set G := fun α => A ∩ ((r α : Q) : G) • (H₁ : Set G)
  have hPmeas : ∀ α, MeasurableSet (P α) := fun α =>
    hA.inter (hH₁.measurableSet.const_smul _)
  have hPunion : A ∩ ((Q : Set G) * (H₁ : Set G)) = ⋃ α, P α := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, P]
    constructor
    · rintro ⟨hxA, q, hq, h, hh, rfl⟩
      refine ⟨QuotientGroup.mk ⟨q, hq⟩, hxA, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      have hO' : ((r (QuotientGroup.mk ⟨q, hq⟩))⁻¹ * ⟨q, hq⟩ : Q) ∈ O := by
        rw [← QuotientGroup.eq, hr]
      have hO'' : ((r (QuotientGroup.mk ⟨q, hq⟩) : Q) : G)⁻¹ * q ∈ H₁ := hO'
      simpa [mul_assoc] using H₁.mul_mem hO'' hh
    · rintro ⟨α, hxA, hx⟩
      refine ⟨hxA, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
      exact ⟨(r α : G), (r α).2, ((r α : Q) : G)⁻¹ * x, hx, by group⟩
  have hPdisj : Pairwise (Function.onFun Disjoint P) := by
    intro α β hαβ
    refine Set.disjoint_left.mpr fun x hxα hxβ => hαβ ?_
    have h1 := (hmemG α x hxα.2 (r α)).mp (by
      have := hxα.2
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at this
      exact this)
    have h2 := (hmemG β x hxβ.2 (r α)).mp (by
      have := hxα.2
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at this
      exact this)
    exact h1.symm.trans h2
  -- each piece
  let AQ : Set Q := (Subtype.val : Q → G) ⁻¹' A
  have hpiece : ∀ α, μ (P α) = c * μQ (AQ ∩ (r α) • (O : Set Q)) := by
    intro α
    set g : G := ((r α : Q) : G)
    -- translate the piece into `H₁`
    have hPα : P α = g • (g⁻¹ • A ∩ (H₁ : Set G)) := by
      change A ∩ g • (H₁ : Set G) = _
      rw [Set.smul_set_inter, smul_inv_smul]
    let S : Set H₁ := H₁.subtype ⁻¹' (g⁻¹ • A)
    have hSimg : H₁.subtype '' S = g⁻¹ • A ∩ (H₁ : Set G) := by
      simp only [S, Set.image_preimage_eq_inter_range, Subgroup.coe_subtype,
        Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq]
    have hSmeas : MeasurableSet S :=
      measurable_subtype_coe (hA.const_smul g⁻¹)
    have hSsat : ∀ a ∈ S, ∀ k ∈ K₁, a * k ∈ S := by
      intro a ha k hk
      change ((a : G) * (k : G)) ∈ g⁻¹ • A
      have ha : (a : G) ∈ g⁻¹ • A := ha
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_inv] at ha ⊢
      have := hAK _ ha _ (Subgroup.mem_subgroupOf.mp hk)
      simpa [mul_assoc] using this
    -- the trace on `Q₁`, read in `Q`
    have hT : ι '' ((Subtype.val : Q₁ → H₁) ⁻¹' S) = (r α)⁻¹ • (AQ ∩ (r α) • (O : Set Q)) := by
      ext q
      simp only [Set.mem_image, Set.mem_preimage, Set.smul_set_inter, inv_smul_smul, S, AQ]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul]
          change g * ((x : H₁) : G) ∈ A
          have := hx
          change ((x : H₁) : G) ∈ g⁻¹ • A at this
          rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul] at this
          exact this
        · exact (x : H₁).2
      · rintro ⟨hqA, hqO⟩
        refine ⟨⟨⟨q, hqO⟩, Subgroup.mem_subgroupOf.mpr q.2⟩, ?_, rfl⟩
        change (q : G) ∈ g⁻¹ • A
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul]
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul] at hqA
        exact hqA
    calc μ (P α) = μ (g⁻¹ • A ∩ (H₁ : Set G)) := by rw [hPα, measure_smul]
      _ = μ₁ S := by
          rw [← hSimg]
          exact (hemb₁.measurableEmbedding.comap_apply μ S).symm
      _ = c * μQ₁ ((Subtype.val : Q₁ → H₁) ⁻¹' S) := hc S hSmeas hSsat
      _ = c * μQ (ι '' ((Subtype.val : Q₁ → H₁) ⁻¹' S)) := by
          rw [hι.measurableEmbedding.comap_apply]
      _ = c * μQ (AQ ∩ (r α) • (O : Set Q)) := by rw [hT, measure_smul]
  -- the pieces in `Q`
  have hQmeas : ∀ α, MeasurableSet (AQ ∩ (r α) • (O : Set Q)) := fun α =>
    (measurable_subtype_coe hA).inter (hO.measurableSet.const_smul _)
  have hQdisj : Pairwise (Function.onFun Disjoint (fun α => AQ ∩ (r α) • (O : Set Q))) := by
    intro α β hαβ
    refine Set.disjoint_left.mpr fun q hqα hqβ => hαβ ?_
    exact ((hmemQ α q).mp hqα.2).symm.trans ((hmemQ β q).mp hqβ.2)
  have hQunion : (⋃ α, AQ ∩ (r α) • (O : Set Q)) = AQ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨QuotientGroup.mk q, h, (hmemQ _ q).mpr rfl⟩⟩
  calc μ (A ∩ ((Q : Set G) * (H₁ : Set G))) = μ (⋃ α, P α) := by rw [hPunion]
    _ = ∑' α, μ (P α) := measure_iUnion hPdisj hPmeas
    _ = ∑' α, c * μQ (AQ ∩ (r α) • (O : Set Q)) := by simp only [hpiece]
    _ = c * ∑' α, μQ (AQ ∩ (r α) • (O : Set Q)) := ENNReal.tsum_mul_left
    _ = c * μQ AQ := by rw [← measure_iUnion hQdisj hQmeas, hQunion]

end Langlands.CompactFactorization
