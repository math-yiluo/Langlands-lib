import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicCoordinates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration
import Langlands.Analysis.Local.CompactFactorizationBochner

/-! # Haar factorization in the coordinates of an idempotent parabolic -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open MeasureTheory Set _root_.Topology
open scoped ENNReal

universe u v

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

variable [TopologicalSpace A] [MeasurableSpace A] [MeasurableSpace Aˣ]
  [MeasurableSpace (Subalgebra.centralizer F ({e} : Set A))ˣ]

/-- Haar factorization in Levi, upper-corner and compact-group coordinates. -/
def IdempotentParabolicHaarFactorizationStatement (he : IsIdempotentElem e) (K : OpenSubgroup Aˣ)
    (μG : Measure Aˣ) (μM : Measure Leviˣ) (μU : Measure Upper) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (μM.prod (μU.prod (μG.comap (K.toSubgroup.subtype : K →* Aˣ)))).map
      (fun p : Leviˣ × (Upper × K) =>
        Units.map (Levi).val.toMonoidHom p.1 * (upperCornerUnit F he p.2.1 * p.2.2.val)) =
      c • μG

variable [FiniteDimensional F A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [BorelSpace A]
  [BorelSpace Aˣ] [BorelSpace (Subalgebra.centralizer F ({e} : Set A))ˣ]

local instance : SecondCountableTopology Aˣ := by
  have : SecondCountableTopology Aᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance (S : Subgroup Aˣ) : SecondCountableTopology S :=
  (IsEmbedding.subtypeVal (p := fun g => g ∈ S)).secondCountableTopology

omit [MeasurableSpace A] [MeasurableSpace (Subalgebra.centralizer F ({e} : Set A))ˣ]
  [BorelSpace A] [BorelSpace (Subalgebra.centralizer F ({e} : Set A))ˣ] in
private theorem map_mul_compactCoordinates (he : IsIdempotentElem e) (K : OpenSubgroup Aˣ)
    (hfac : ∀ g : Aˣ, ∃ p ∈ parabolicUnits F he, ∃ k ∈ K, g = p * k)
    (μG : Measure Aˣ) [μG.IsHaarMeasure]
    (νM : Measure (leviUnits F (e := e))) [νM.IsHaarMeasure] [SFinite νM]
    (νU : Measure (upperCornerUnits F he)) [νU.IsHaarMeasure] [SFinite νU]
    (μK : Measure K)
    (hνK : μK.map Subtype.val = μG.restrict (K : Set Aˣ)) :
    (μK.prod (νM.prod νU)).map
      (fun p : K × (leviUnits F (e := e) × upperCornerUnits F he) =>
        (p.2.1.val * p.2.2.val) * p.1.val) =
      (νM.prod νU) (HarishChandraSchwartz.leviUnipotentMul ⁻¹' (K : Set Aˣ)) • μG := by
  let ι := HarishChandraSchwartz.leviUnipotentMul (M := leviUnits F (e := e))
    (U := upperCornerUnits F he)
  have hι : Measurable ι := HarishChandraSchwartz.continuous_leviUnipotentMul.measurable
  have hshift := leviUnits_le_normalizer_upperCornerUnits F he
  have hmul : Measurable (CompactFactorization.factorizationMap ι) :=
    (hι.comp measurable_snd).mul measurable_fst
  change (μK.prod (νM.prod νU)).map
      (CompactFactorization.factorizationMap ι ∘ Prod.map Subtype.val id) =
    (νM.prod νU) (ι ⁻¹' (K : Set Aˣ)) • μG
  rw [← Measure.map_map hmul (measurable_subtype_coe.prodMap measurable_id),
    ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, hνK, Measure.map_id]
  apply CompactFactorization.map_restrict_prod_mul μG K.toSubgroup K.isOpen.measurableSet
    (νM.prod νU) ι hι
  · intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hfac g
    let x := (parabolicUnitsHomeomorph F he).symm ⟨p, hp⟩
    refine ⟨x, k, hk, ?_⟩
    have h := congrArg Subtype.val ((parabolicUnitsHomeomorph F he).apply_symm_apply ⟨p, hp⟩)
    change (parabolicUnitsHomeomorph F he x).val = p at h
    rw [parabolicUnitsHomeomorph_apply_val] at h
    change g = (x.1.val * x.2.val) * k
    rw [h, hg]
  · intro x₀
    exact ⟨HarishChandraSchwartz.leviUnipotentShift hshift x₀,
      HarishChandraSchwartz.measurePreserving_leviUnipotentShift hshift x₀,
      HarishChandraSchwartz.leviUnipotentMul_shift hshift x₀⟩

/-- If the parabolic and a compact open subgroup multiply onto the ambient unit group,
the product of the indicated Haar measures pushes forward to a positive finite multiple
of ambient Haar. -/
theorem idempotentParabolicHaarFactorization (he : IsIdempotentElem e) (K : OpenSubgroup Aˣ)
    (hK : IsCompact (K : Set Aˣ))
    (hfac : ∀ g : Aˣ, ∃ p ∈ parabolicUnits F he, ∃ k ∈ K, g = p * k)
    (μG : Measure Aˣ) [μG.IsHaarMeasure]
    (μM : Measure Leviˣ) [μM.IsHaarMeasure] [SFinite μM]
    (μU : Measure Upper) [μU.IsAddHaarMeasure] [SFinite μU] :
    IdempotentParabolicHaarFactorizationStatement F he K μG μM μU := by
  let : MeasurableSpace (Multiplicative Upper) := inferInstanceAs (MeasurableSpace Upper)
  let : BorelSpace (Multiplicative Upper) := inferInstanceAs (BorelSpace Upper)
  let μU' : Measure (Multiplicative Upper) := μU
  have : SFinite μU' := inferInstanceAs (SFinite μU)
  have : μU'.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts μU)
      map_mul_left_eq_self := fun z => map_add_left_eq_self μU z.toAdd
      toIsOpenPosMeasure := inferInstanceAs (μU.IsOpenPosMeasure) }
  let E := leviUnitsEquiv F (e := e)
  let D := upperCornerUnitsEquiv F he
  let νM := μM.map E
  let νU := μU'.map D
  have : νM.IsHaarMeasure := E.isHaarMeasure_map μM
  have : νU.IsHaarMeasure := D.isHaarMeasure_map μU'
  have : SFinite νM := inferInstanceAs (SFinite (μM.map E))
  have : SFinite νU := inferInstanceAs (SFinite (μU'.map D))
  let μK := μG.comap (K.toSubgroup.subtype : K →* Aˣ)
  have : μK.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (f := K.toSubgroup.subtype) μG
      K.isOpen.isOpenEmbedding_subtypeVal
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have hνK : μK.map Subtype.val = μG.restrict (K : Set Aˣ) :=
    map_comap_subtype_coe K.isOpen.measurableSet μG
  let ι := HarishChandraSchwartz.leviUnipotentMul (M := leviUnits F (e := e))
    (U := upperCornerUnits F he)
  have hι : Continuous ι := HarishChandraSchwartz.continuous_leviUnipotentMul
  let c := (νM.prod νU) (ι ⁻¹' (K : Set Aˣ))
  have hop : IsOpen (ι ⁻¹' (K : Set Aˣ)) := K.isOpen.preimage hι
  have hne : (ι ⁻¹' (K : Set Aˣ)).Nonempty := by
    refine ⟨(1, 1), ?_⟩
    change (1 : Aˣ) * 1 ∈ K
    rw [mul_one]
    exact K.one_mem
  have hcomp : IsCompact (ι ⁻¹' (K : Set Aˣ)) :=
    (parabolicUnitsHomeomorph F he).isCompact_preimage.mpr
      ((isClosed_parabolicUnits F he).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  refine ⟨c, (hop.measure_pos _ hne).ne', hcomp.measure_ne_top, ?_⟩
  let T (p : K × (leviUnits F (e := e) × upperCornerUnits F he)) :=
    ι p.2 * p.1.val
  have hT : Measurable T :=
    (hι.measurable.comp measurable_snd).mul (measurable_subtype_coe.comp measurable_fst)
  let S (p : Leviˣ × (Upper × K)) := (p.2.2, (E p.1, D (Multiplicative.ofAdd p.2.1)))
  have hE : MeasurePreserving E μM νM := ⟨E.continuous.measurable, rfl⟩
  have hD : MeasurePreserving (fun z : Upper => D (Multiplicative.ofAdd z)) μU νU :=
    ⟨D.continuous.measurable, rfl⟩
  have hR : MeasurePreserving (fun p : Leviˣ × (Upper × K) => (p.2.2, (p.1, p.2.1)))
      (μM.prod (μU.prod μK)) (μK.prod (μM.prod μU)) :=
    Measure.measurePreserving_swap.comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μM μU μK))
  have hS : MeasurePreserving S (μM.prod (μU.prod μK)) (μK.prod (νM.prod νU)) :=
    ((MeasurePreserving.id μK).prod (hE.prod hD)).comp hR
  change (μM.prod (μU.prod μK)).map (fun p : Leviˣ × (Upper × K) =>
    Units.map (Levi).val.toMonoidHom p.1 * (upperCornerUnit F he p.2.1 * p.2.2.val)) = c • μG
  have hTS : (fun p : Leviˣ × (Upper × K) =>
      Units.map (Levi).val.toMonoidHom p.1 * (upperCornerUnit F he p.2.1 * p.2.2.val)) =
      T ∘ S := by
    funext p
    change _ = (_ * _) * _
    rw [mul_assoc]
    rfl
  rw [hTS, ← Measure.map_map hT hS.measurable, hS.map_eq]
  exact map_mul_compactCoordinates F he K hfac μG νM νU μK hνK

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
