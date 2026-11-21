import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Mathlib.MeasureTheory.Measure.Prod

/-! # Product coordinates for a compact open quotient orbit -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Topology

namespace Langlands.QuotientIntegration

universe u v

/-- Exact product Haar coordinates on a compact open subgroup descend to
the given compatible measure on its orbit in the left quotient. -/
abbrev CompactOpenQuotientChartStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
      (μG : Measure G) [IsHaarMeasure μG] [μG.Regular]
      (μH : Measure H) [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (ν : Measure (LeftQuotient H)), IsCompatible H μG μH ν →
    ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
      let A := K.comap H.subtype continuous_subtype_val
      ∀ {X : Type v} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
        [MeasurableSpace A] [BorelSpace A]
        (μX : Measure X) [SFinite μX] (s : X → K) (m : A × X ≃ₜ K),
        (∀ p : A × X, (m p : G) = (p.1.val : G) * (s p.2 : G)) →
        ((μH.comap A.subtype).prod μX).map (fun p => (m p : G)) = μG.restrict (K : Set G) →
        let c := fun x : X => leftQuotientMap H (s x : G)
        IsOpenEmbedding c ∧ Set.range c = leftQuotientMap H '' (K : Set G) ∧
          μX.map c = ν.restrict (Set.range c)

theorem compactOpenQuotientChart : CompactOpenQuotientChartStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ _ _ μG _ _ μH _ _ _ ν hν K hK
  let A := K.comap H.subtype continuous_subtype_val
  dsimp only
  intro X _ _ _ _ _ μX _ s m hm hprod
  let : SecondCountableTopology H :=
    TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  let : SecondCountableTopology A :=
    TopologicalSpace.Subtype.secondCountableTopology (A : Set H)
  let q := leftQuotientMap H
  let c := fun x : X => q (s x : G)
  let f : A × X → G := fun p => (m p : G)
  have hq := leftQuotient_isOpenQuotientMap H
  have hf : IsOpenEmbedding f :=
    K.isOpen.isOpenEmbedding_subtypeVal.comp m.isOpenEmbedding
  have hcomm : q ∘ f = c ∘ Prod.snd := by
    funext p
    change q (m p : G) = q (s p.2 : G)
    rw [hm]
    exact leftQuotientMap_subgroup_mul H p.1.val _
  have hcont : Continuous c := by
    have heq : c = (q ∘ f) ∘ fun x : X => ((1 : A), x) := by rw [hcomm]; rfl
    rw [heq]
    exact (hq.continuous.comp hf.continuous).comp (continuous_const.prodMk continuous_id)
  have hopen : IsOpenMap c := by
    apply IsOpenMap.of_comp continuous_snd (fun x => ⟨((1 : A), x), rfl⟩)
    rw [← hcomm]
    exact hq.isOpenMap.comp hf.isOpenMap
  have hinj : Function.Injective c := by
    intro x y hxy
    let g : G := (s y : G) * (s x : G)⁻¹
    have hgH : g ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
    have hgK : g ∈ K := K.mul_mem (s y).property (K.inv_mem (s x).property)
    let a : A := ⟨⟨g, hgH⟩, hgK⟩
    have heq : (m (a, x) : G) = (m (1, y) : G) := by
      rw [hm, hm]
      change g * (s x : G) = 1 * (s y : G)
      simp [g, mul_assoc]
    exact congrArg Prod.snd (m.injective (Subtype.ext heq))
  have hrange : Set.range c = q '' (K : Set G) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(s x : G), (s x).property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp⟩ := m.surjective (⟨g, hg⟩ : K)
      exact ⟨p.2, (congrFun hcomm p).symm.trans (congrArg (q ∘ Subtype.val) hp)⟩
  refine ⟨IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen, hrange, ?_⟩
  obtain ⟨hpos, hfin, hmass⟩ := compactOpenOrbitMeasure H hH μG μH K hK ν hν (1 : G)
  simp only [inv_one, one_mul, mul_one] at hpos hfin hmass
  let μA : Measure A := μH.comap A.subtype
  have huniv : μA Set.univ = μH {h : H | (h : G) ∈ K} := by
    have hAe : MeasurableEmbedding (A.subtype : A → H) :=
      A.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
    rw [hAe.comap_apply, Set.image_univ]
    change μH (Set.range (Subtype.val : A → H)) = μH (A : Set H)
    rw [Subtype.range_coe]
  have hqmap : (μG.restrict (K : Set G)).map q = (μA Set.univ) • μX.map c := by
    rw [← hprod, Measure.map_map hq.continuous.measurable hf.continuous.measurable, hcomm,
      ← Measure.map_map hcont.measurable measurable_snd, Measure.map_snd_prod,
      Measure.map_smul _ hcont.measurable.aemeasurable]
  rw [hrange, hmass, ← huniv, hqmap, smul_smul,
    ENNReal.inv_mul_cancel (huniv ▸ hpos.ne') (huniv ▸ hfin.ne), one_smul]

end Langlands.QuotientIntegration
