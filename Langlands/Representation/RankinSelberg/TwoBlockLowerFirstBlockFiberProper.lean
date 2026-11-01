import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper

/-!
# Compact finiteness of the actual lower mixed fiber kernels
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockJacquet TwoBlockDeformation Set

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩


/-- The right radical coordinate of a lower mixed matrix. -/
def rightRadicalCoord (l : lowerMixedSubgroup F h) :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier :=
  (((lowerMixedCoordinates F h l).2.2.val)⁻¹).val * entryBlock h F.Carrier l.val 1 0

theorem continuous_rightRadicalCoord : Continuous (rightRadicalCoord F h) := by
  have hd := (continuous_snd.comp (continuous_snd.comp
    (lowerMixedSubgroupHomeomorph F h).continuous_invFun))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp hd).inv).matrix_mul
    ((continuous_entryBlock h F.Carrier 1 0).comp continuous_subtype_val)

/-- The coordinate recovers the radical after any diagonal mixed factor. -/
theorem rightRadicalCoord_mixed_mul_radical (b : mixedSubgroup F h)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
    rightRadicalCoord F h
      ⟨b.val * lowerRadical h F.Carrier Z,
        mul_mem (mixedSubgroup_le_lowerMixedSubgroup F h b.property)
          (lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F.Carrier Z))⟩ = Z := by
  rcases b with ⟨b, ⟨d, rfl⟩⟩
  have he : (⟨mixedEmbedding F h d * lowerRadical h F.Carrier Z,
      mul_mem (mixedSubgroup_le_lowerMixedSubgroup F h ⟨d, rfl⟩)
        (lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F.Carrier Z))⟩ :
      lowerMixedSubgroup F h) =
      lowerMixedSubgroupEquiv F h (d.2.val.val * Z * (d.1.val⁻¹).val, d) :=
    Subtype.ext (leviEmbedding_blockPair_mul_lowerRadical h F.Carrier d.1.val d.2.val Z)
  rw [he]
  change (((lowerMixedDiagonal F h ⟨lowerProduct h F.Carrier
    (d.2.val.val * Z * (d.1.val⁻¹).val) d.1.val d.2.val, _⟩).2.val)⁻¹).val *
    entryBlock h F.Carrier
      (lowerProduct h F.Carrier (d.2.val.val * Z * (d.1.val⁻¹).val) d.1.val d.2.val) 1 0 = Z
  rw [lowerMixedDiagonal_lowerProduct, entryBlock_lowerProduct_one_zero]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- A continuous coordinate recovering every left coset fiber makes the fiber proper. -/
theorem quotientFiber_isCompact_preimage_of_coordinate
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    {X : Type*} [TopologicalSpace X]
    (H L : Subgroup G) (hH : IsClosed (H : Set G)) (hL : IsClosed (L : Set G))
    (hHL : H ≤ L) (f : X → G) (hf : Continuous f) (hfL : ∀ x, f x ∈ L)
    (r : L → X) (hr : Continuous r)
    (hrf : ∀ (b : H) x, r ⟨b.val * f x, mul_mem (hHL b.property) (hfL x)⟩ = x)
    (g : G) {S : Set (LeftQuotient H)} (hS : IsCompact S) :
    IsCompact ((fun x => leftQuotientMap H (f x * g)) ⁻¹' S) := by
  let := leftQuotient_t2Space H hH
  obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H hH hS
  let D : Set L := Subtype.val ⁻¹' ((fun c => c * g⁻¹) '' C)
  have hD : IsCompact D := hL.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hC.image (continuous_id.mul continuous_const))
  have hcont : Continuous (fun x => leftQuotientMap H (f x * g)) :=
    continuous_quotient_mk'.comp (hf.mul continuous_const)
  refine (hD.image hr).of_isClosed_subset (hS.isClosed.preimage hcont) ?_
  intro x hx
  have hxC : leftQuotientMap H (f x * g) ∈ leftQuotientMap H '' C := by rwa [hCS]
  obtain ⟨c, hc, hcx⟩ := hxC
  have hb : c * (f x * g)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcx.symm)
  let b : H := ⟨c * (f x * g)⁻¹, hb⟩
  have hn : c * g⁻¹ = b.val * f x := by
    dsimp [b]
    group
  let l : L := ⟨b.val * f x, mul_mem (hHL hb) (hfL x)⟩
  exact ⟨l, ⟨c, hc, hn⟩, hrf b x⟩

/-- Radical fibers have compact preimages of compact sets in the mixed quotient. -/
theorem radicalFiberPoint_isCompact_preimage (g : GeneralLinear (t + 1) F.Carrier)
    {S : Set (MixedQuotient F h)} (hS : IsCompact S) :
    IsCompact ((fun Z => radicalFiberPoint F h Z g) ⁻¹' S) :=
  quotientFiber_isCompact_preimage_of_coordinate
    (mixedSubgroup F h) (lowerMixedSubgroup F h)
    (isClosed_mixedSubgroup F h) (isClosed_lowerMixedSubgroup F h)
    (mixedSubgroup_le_lowerMixedSubgroup F h) (lowerRadical h F.Carrier)
    (continuous_lowerRadical h F.Carrier)
    (fun Z => lowerBlockUnipotent_le_lowerMixedSubgroup F h (lowerRadical_mem h F.Carrier Z))
    (rightRadicalCoord F h) (continuous_rightRadicalCoord F h)
    (rightRadicalCoord_mixed_mul_radical F h) g hS

/-- The small quotient of the first diagonal coordinate. -/
def lowerMixedFirstQuotient (l : lowerMixedSubgroup F h) :
    LeftUnipotentQuotient (m 0) F.Carrier :=
  Quotient.mk _ ((lowerMixedSubgroupEquiv F h).symm l).2.1.val

theorem continuous_lowerMixedFirstQuotient : Continuous (lowerMixedFirstQuotient F h) :=
  continuous_quotient_mk'.comp (continuous_subtype_val.comp
    (continuous_fst.comp (continuous_snd.comp (lowerMixedSubgroupHomeomorph F h).continuous_invFun)))

/-- Multiplication from the lower unipotent subgroup leaves the first quotient unchanged. -/
theorem lowerMixedFirstQuotient_lower_mul (b : lowerBlockUnipotent h F.Carrier)
    (u : normOneSubgroup F (m 0 + 1)) :
    lowerMixedFirstQuotient F h
      ⟨b.val * firstBlockEmbedding h F.Carrier u.val,
        mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h b.property)
          (mixedSubgroup_le_lowerMixedSubgroup F h
            (firstBlockEmbedding_mem_mixedSubgroup F h u))⟩ = Quotient.mk _ u.val := by
  have he : ((lowerMixedSubgroupEquiv F h).symm
      ⟨b.val * firstBlockEmbedding h F.Carrier u.val,
        mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h b.property)
          (mixedSubgroup_le_lowerMixedSubgroup F h
            (firstBlockEmbedding_mem_mixedSubgroup F h u))⟩).2.1.val =
      (diagonalBlocks h F.Carrier b 0).val * u.val := by
    apply Units.ext
    rw [lowerMixedSubgroupEquiv_symm_apply_fst, Units.val_mul,
      entryBlock_mul, firstBlockEmbedding_apply]
    simp only [entryBlock_levi_zero_zero, entryBlock_levi_one_zero,
      Matrix.mul_zero, add_zero]
    rfl
  unfold lowerMixedFirstQuotient
  rw [he]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _
    (diagonalBlocks h F.Carrier b 0).property u.val

/-- First-block fibers restricted to one determinant slice have compact preimages. -/
theorem firstBlockFiberPoint_slice_isCompact_preimage (k : ℤ)
    (g : GeneralLinear (t + 1) F.Carrier)
    {S : Set (LowerQuotient h F.Carrier)} (hS : IsCompact S) :
    IsCompact (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k ∩
      (fun q => firstBlockFiberPoint F h q g) ⁻¹' S) := by
  classical
  let H := lowerBlockUnipotent h F.Carrier
  let L := lowerMixedSubgroup F h
  let := leftQuotient_t2Space H (isClosed_lowerBlockUnipotent_canonical F h)
  let B := RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k ∩
    (fun q => firstBlockFiberPoint F h q g) ⁻¹' S
  by_cases hB : B.Nonempty
  · obtain ⟨q0, hq0⟩ := hB
    induction q0 using Quotient.inductionOn with
    | h u0 =>
      obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H
        (isClosed_lowerBlockUnipotent_canonical F h) hS
      let D : Set L := Subtype.val ⁻¹'
        ((fun c => c * g⁻¹ * (firstBlockEmbedding h F.Carrier u0)⁻¹) '' C)
      have hD : IsCompact D :=
        (isClosed_lowerMixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
          (hC.image ((continuous_id.mul continuous_const).mul continuous_const))
      let ψ : L → LeftUnipotentQuotient (m 0) F.Carrier :=
        fun l => rightTranslate _ u0 (lowerMixedFirstQuotient F h l)
      have hψ : Continuous ψ :=
        (rightTranslate _ u0).continuous.comp (continuous_lowerMixedFirstQuotient F h)
      have hf : Continuous (fun q => firstBlockFiberPoint F h q g) :=
        (continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)
      apply (hD.image hψ).of_isClosed_subset
        ((RankinSelberg.isClosed_determinantSlice F.canonicalTopologicalData (m 0) k).inter
          (hS.isClosed.preimage hf))
      intro q hq
      induction q using Quotient.inductionOn with
      | h u =>
        have huv : F.canonicalTopologicalData.ord (GeneralLinear.determinant u : F.Carrier) =
            F.canonicalTopologicalData.ord (GeneralLinear.determinant u0 : F.Carrier) :=
          hq.1.trans hq0.1.symm
        let v : normOneSubgroup F (m 0 + 1) :=
          ⟨u * u0⁻¹, mul_inv_mem_normOne_of_ord_eq F u u0 huv⟩
        have hxC : firstBlockFiberPoint F h (Quotient.mk _ u) g ∈ leftQuotientMap H '' C := by
          rw [hCS]
          exact hq.2
        obtain ⟨c, hc, hcu⟩ := hxC
        have hb : c * (firstBlockEmbedding h F.Carrier u * g)⁻¹ ∈ H :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact hcu.symm)
        let b : H := ⟨c * (firstBlockEmbedding h F.Carrier u * g)⁻¹, hb⟩
        have he : c * g⁻¹ * (firstBlockEmbedding h F.Carrier u0)⁻¹ =
            b.val * firstBlockEmbedding h F.Carrier v.val := by
          dsimp [b, v]
          simp only [map_mul, map_inv, mul_inv_rev]
          group
        let l : L := ⟨b.val * firstBlockEmbedding h F.Carrier v.val,
          mul_mem (lowerBlockUnipotent_le_lowerMixedSubgroup F h hb)
            (mixedSubgroup_le_lowerMixedSubgroup F h
              (firstBlockEmbedding_mem_mixedSubgroup F h v))⟩
        refine ⟨l, ⟨c, hc, he⟩, ?_⟩
        change rightTranslate _ u0 (lowerMixedFirstQuotient F h l) = Quotient.mk _ u
        rw [lowerMixedFirstQuotient_lower_mul F h b v, rightTranslate_mk]
        simp [v, mul_assoc]
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    change IsCompact B
    rw [he]
    exact isCompact_empty

section RadicalKernel

variable (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
  [μR.IsAddHaarMeasure]

/-- Every radical kernel measure is finite on compact sets. -/
theorem radicalKernel_compact_ne_top (q : LowerMixedQuotient F h)
    (S : Set (MixedQuotient F h)) (hS : IsCompact S) :
    radicalKernel F h μR q S ≠ ⊤ := by
  let := leftQuotient_t2Space (mixedSubgroup F h) (isClosed_mixedSubgroup F h)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun Z => radicalFiberPoint F h Z g) :=
      ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [radicalKernel_mk F h μR g, Measure.map_apply hf hS.measurableSet]
    exact (radicalFiberPoint_isCompact_preimage F h g hS).measure_ne_top

/-- Compact finiteness on a common countable compact cover gives radical kernel s-finiteness. -/
theorem radicalKernel_isSFinite : IsSFiniteKernel (radicalKernel F h μR) := by
  let H := mixedSubgroup F h
  let := leftQuotient_t2Space H (isClosed_mixedSubgroup F h)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (radicalKernel F h μR)
    (radicalKernel_compact_ne_top F h μR)

end RadicalKernel

section FirstBlockKernel

variable (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
  [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)

/-- Every first-block slice kernel measure is finite on compact sets. -/
theorem firstBlockKernel_compact_ne_top (k : ℤ) (q : LowerMixedQuotient F h)
    (S : Set (LowerQuotient h F.Carrier)) (hS : IsCompact S) :
    firstBlockKernel F h νA hνA k q S ≠ ⊤ := by
  let := leftQuotient_t2Space (lowerBlockUnipotent h F.Carrier)
    (isClosed_lowerBlockUnipotent_canonical F h)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun q => firstBlockFiberPoint F h q g) :=
      ((continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockKernel_mk F h νA hνA k g, Measure.map_apply hf hS.measurableSet,
      Measure.restrict_apply (hf hS.measurableSet), Set.inter_comm]
    exact (firstBlockFiberPoint_slice_isCompact_preimage F h k g hS).measure_ne_top

/-- Compact finiteness on a common countable compact cover gives first-block kernel s-finiteness. -/
theorem firstBlockKernel_isSFinite (k : ℤ) :
    IsSFiniteKernel (firstBlockKernel F h νA hνA k) := by
  let H := lowerBlockUnipotent h F.Carrier
  let := leftQuotient_t2Space H (isClosed_lowerBlockUnipotent_canonical F h)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (firstBlockKernel F h νA hνA k)
    (firstBlockKernel_compact_ne_top F h νA hνA k)

end FirstBlockKernel

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
