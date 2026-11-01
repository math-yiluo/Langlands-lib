import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Langlands.Analysis.Local.QuotientKernelSupport
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Properness on first-block determinant slices
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  borel _
local instance : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (MixedQuotient F h) := borel _
local instance : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

open Set TwoBlockJacquet TwoBlockDeformation

/-- The first block of a mixed element, viewed on the small quotient. -/
def mixedFirstQuotient (l : mixedSubgroup F h) : LeftUnipotentQuotient (m 0) F.Carrier :=
  Quotient.mk _ ((mixedSubgroupEquiv F h).symm l).1.val

theorem continuous_mixedFirstQuotient : Continuous (mixedFirstQuotient F h) :=
  continuous_quotient_mk'.comp
    (continuous_subtype_val.comp (continuous_fst.comp (mixedSubgroupHomeomorph F h).continuous_invFun))

/-- Norm-one first-block matrices embed in the actual mixed subgroup. -/
theorem firstBlockEmbedding_mem_mixedSubgroup (u : normOneSubgroup F (m 0 + 1)) :
    firstBlockEmbedding h F.Carrier u.val ∈ mixedSubgroup F h :=
  ⟨(u, 1), rfl⟩

/-- Equal determinant orders put the ratio in the norm-one subgroup. -/
theorem mul_inv_mem_normOne_of_ord_eq (u v : GeneralLinear (m 0 + 1) F.Carrier)
    (huv : F.canonicalTopologicalData.ord (GeneralLinear.determinant u : F.Carrier) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant v : F.Carrier)) :
    u * v⁻¹ ∈ normOneSubgroup F (m 0 + 1) := by
  rw [mem_normOneSubgroup_iff_normalizedAbs, ← Matrix.GeneralLinearGroup.val_det_apply,
    ← F.canonicalTopologicalData.ord_eq_zero_iff_normalizedAbs]
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant u).ne_zero
      (inv_ne_zero (GeneralLinear.determinant v).ne_zero),
    F.canonicalTopologicalData.ord_inv, huv, add_neg_cancel]

/-- The quotient of the first coordinate ignores the first unipotent block. -/
theorem mixedFirstQuotient_block_mul (b : TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
    (u : normOneSubgroup F (m 0 + 1)) :
    mixedFirstQuotient F h
      ⟨b.val * firstBlockEmbedding h F.Carrier u.val,
        mul_mem (blockUnipotent_le_mixedSubgroup F h b.property)
          (firstBlockEmbedding_mem_mixedSubgroup F h u)⟩ = Quotient.mk _ u.val := by
  obtain ⟨n, hn⟩ := b.property
  let n0 : normOneSubgroup F (m 0 + 1) :=
    ⟨(n 0).val, determinantNorm_eq_one_of_mem_upperUnipotent F
      F.canonicalTopologicalData (n 0).property⟩
  have he : b.val * firstBlockEmbedding h F.Carrier u.val =
      mixedEmbedding F h (n0 * u, n 1) := by
    rw [← hn, TwoBlockUnipotentQuotient.blockEmbedding_apply,
      firstBlockEmbedding_apply, mixedEmbedding_apply, ← map_mul]
    apply congrArg ((succBlockShape m h).leviEmbedding F.Carrier)
    funext i
    fin_cases i <;> simp [blockPair, n0]
  have hs : (⟨b.val * firstBlockEmbedding h F.Carrier u.val,
      mul_mem (blockUnipotent_le_mixedSubgroup F h b.property)
        (firstBlockEmbedding_mem_mixedSubgroup F h u)⟩ : mixedSubgroup F h) =
      mixedSubgroupEquiv F h (n0 * u, n 1) := Subtype.ext he
  rw [hs]
  change Quotient.mk _ (((mixedSubgroupEquiv F h).symm
    (mixedSubgroupEquiv F h (n0 * u, n 1))).1.val) = _
  rw [MulEquiv.symm_apply_apply]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem _ (n 0).property u.val

/-- Restricted first-block fibers have compact preimages of compact sets. -/
theorem fiberPoint_slice_isCompact_preimage (k : ℤ) (g : GeneralLinear (t + 1) F.Carrier)
    {S : Set (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)} (hS : IsCompact S) :
    IsCompact (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k ∩
      (fun q => fiberPoint h F.Carrier q g) ⁻¹' S) := by
  classical
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
  let L := mixedSubgroup F h
  let := leftQuotient_t2Space H (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
  let B := RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k ∩
    (fun q => fiberPoint h F.Carrier q g) ⁻¹' S
  by_cases hB : B.Nonempty
  · obtain ⟨q0, hq0⟩ := hB
    induction q0 using Quotient.inductionOn with
    | h u0 =>
      obtain ⟨C, hC, hCS⟩ := leftQuotient_exists_isCompact_image H
        (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier) hS
      let D : Set L := Subtype.val ⁻¹'
        ((fun c => c * g⁻¹ * (firstBlockEmbedding h F.Carrier u0)⁻¹) '' C)
      have hD : IsCompact D :=
        (isClosed_mixedSubgroup F h).isClosedEmbedding_subtypeVal.isCompact_preimage
          (hC.image ((continuous_id.mul continuous_const).mul continuous_const))
      let ψ : L → LeftUnipotentQuotient (m 0) F.Carrier :=
        fun l => rightTranslate _ u0 (mixedFirstQuotient F h l)
      have hψ : Continuous ψ :=
        (rightTranslate _ u0).continuous.comp (continuous_mixedFirstQuotient F h)
      have hf : Continuous (fun q => fiberPoint h F.Carrier q g) :=
        (continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)
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
        have hxC : fiberPoint h F.Carrier (Quotient.mk _ u) g ∈ leftQuotientMap H '' C := by
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
          mul_mem (blockUnipotent_le_mixedSubgroup F h hb)
            (firstBlockEmbedding_mem_mixedSubgroup F h v)⟩
        refine ⟨l, ⟨c, hc, he⟩, ?_⟩
        change rightTranslate _ u0 (mixedFirstQuotient F h l) = Quotient.mk _ u
        rw [mixedFirstQuotient_block_mul F h b v, rightTranslate_mk]
        simp [v, mul_assoc]
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    change IsCompact B
    rw [he]
    exact isCompact_empty

variable (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
  [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)

/-- Each fiber measure is finite on compact sets. -/
theorem fiberKernel_compact_ne_top (k : ℤ) (q : MixedQuotient F h)
    (S : Set (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)) (hS : IsCompact S) :
    fiberKernel F h νA hνA k q S ≠ ⊤ := by
  let := leftQuotient_t2Space (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
    (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
  induction q using Quotient.inductionOn with
  | h g =>
    have hf : Measurable (fun q => fiberPoint h F.Carrier q g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [fiberKernel_mk F h νA hνA k g, Measure.map_apply hf hS.measurableSet,
      Measure.restrict_apply (hf hS.measurableSet), Set.inter_comm]
    exact (fiberPoint_slice_isCompact_preimage F h k g hS).measure_ne_top

/-- Compact finiteness on the common countable compact cover proves kernel s-finiteness. -/
theorem fiberKernel_isSFinite (k : ℤ) : IsSFiniteKernel (fiberKernel F h νA hνA k) := by
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
  let := leftQuotient_t2Space H (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (fiberKernel F h νA hνA k)
    (fiberKernel_compact_ne_top F h νA hνA k)

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
