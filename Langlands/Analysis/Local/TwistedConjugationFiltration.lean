import Langlands.Analysis.Local.TwistedConjugationVectorStep

/-! # Haar scaling through a finite vector filtration -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Langlands.HaarModulus.VectorFiltration

open Langlands.QuotientIntegration

universe u v

attribute [local instance] Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace

/-- The inverse determinant factors for the successive linear displacements. -/
def displacementFiltrationFactor {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ → ℕ}
    (D : ∀ r, (Fin (n r) → k) ≃ₗ[k] (Fin (n r) → k)) (a b : ℕ) : ℝ≥0∞ :=
  ∏ r ∈ Finset.Ico a b, ((distribHaarChar k (LinearEquiv.det (D r)) : ℝ≥0∞))⁻¹

private theorem map_displacement_of_equiv
    {G H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (α : G ≃ₜ* G) (β : H ≃ₜ* H)
    (heα : ∀ x, e (α x) = β (e x)) (μ : Measure G) (c : ℝ≥0∞)
    (h : (μ.map e).map (twistedConjugationMap β) = c • μ.map e) :
    μ.map (twistedConjugationMap α) = c • μ := by
  have he : Measurable (e : G → H) := e.continuous.measurable
  have hes : Measurable (e.symm : H → G) := e.symm.continuous.measurable
  have hα : Measurable (twistedConjugationMap α) := (α.continuous.inv.mul continuous_id).measurable
  have hβ : Measurable (twistedConjugationMap β) := (β.continuous.inv.mul continuous_id).measurable
  have hcomp : twistedConjugationMap β ∘ e = e ∘ twistedConjugationMap α := by
    funext x
    simp only [Function.comp_apply, twistedConjugationMap, map_mul, map_inv, heα]
  have hback := congrArg (Measure.map e.symm) h
  rw [Measure.map_map hβ he, hcomp, ← Measure.map_map he hα, Measure.map_map hes he,
    show (e.symm ∘ e : G → G) = id from funext e.symm_apply_apply, Measure.map_id,
    Measure.map_smul _ hes.aemeasurable, Measure.map_map hes he,
    show (e.symm ∘ e : G → G) = id from funext e.symm_apply_apply, Measure.map_id] at hback
  exact hback

/-- The actual displacement on the first subgroup pushes Haar measure forward
by the product of the inverse determinant factors on a finite filtration.
The filtration is given by its actual vector quotients and the final trivial
subgroup. The conjugating element belongs to the ambient normalizer. -/
theorem map_twistedConjugationMap_of_vectorFiltration
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    (N : ℕ) (F : ℕ → Subgroup G) (hF0 : IsClosed (F 0 : Set G)) (hFN : F N = ⊥)
    (hcover : ∀ x : F 0, ∃ C : OpenSubgroup (F 0), IsCompact (C : Set (F 0)) ∧ x ∈ C)
    (hFle : ∀ r < N, F (r + 1) ≤ F r)
    (g : G) (hg : ∀ r ≤ N, g ∈ Subgroup.normalizer (F r : Set G))
    (n : ℕ → ℕ) (q : ∀ r, F r → Fin (n r) → k)
    (hqmul : ∀ r < N, ∀ x y : F r, q r (x * y) = q r x + q r y)
    (hqker : ∀ r < N, ∀ x : F r, q r x = 0 ↔ (x : G) ∈ F (r + 1))
    (hqc : ∀ r < N, Continuous (q r)) (hqo : ∀ r < N, IsOpenMap (q r))
    (hqs : ∀ r < N, Function.Surjective (q r))
    (D : ∀ r, (Fin (n r) → k) ≃ₗ[k] (Fin (n r) → k))
    (hqD : ∀ r (hr : r < N) (x : F r),
      D r (q r x) = q r x - q r (normalizerConj (F r) ⟨g, hg r hr.le⟩ x))
    (μ : Measure (F 0)) [μ.IsHaarMeasure] :
    μ.map (twistedConjugationMap (normalizerConj (F 0) ⟨g, hg 0 (Nat.zero_le _)⟩)) =
      displacementFiltrationFactor D 0 N • μ := by
  have : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  have hle0 : ∀ r ≤ N, F r ≤ F 0 := by
    intro r hr
    induction r with
    | zero => exact le_rfl
    | succ r ih => exact (hFle r (by omega)).trans (ih (by omega))
  have hclosed : ∀ r ≤ N, IsClosed (F r : Set G) := by
    intro r hr
    induction r with
    | zero => exact hF0
    | succ r ih =>
      have hFr := ih (by omega)
      have hset : (F (r + 1) : Set G) = Subtype.val '' (q r ⁻¹' {0}) := by
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hFle r (by omega) hx⟩, (hqker r (by omega) _).2 hx, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact (hqker r (by omega) y).1 hy
      rw [hset]
      exact hFr.isClosedEmbedding_subtypeVal.isClosedMap _
        (isClosed_singleton.preimage (hqc r (by omega)))
  have hcoverF : ∀ r ≤ N, ∀ x : F r, ∃ C : OpenSubgroup (F r),
      IsCompact (C : Set (F r)) ∧ x ∈ C := by
    intro r hr x
    obtain ⟨C, hC, hxC⟩ := hcover ⟨x, hle0 r hr x.2⟩
    let i : F r →* F 0 := Subgroup.inclusion (hle0 r hr)
    have hi : Continuous i := continuous_subtype_val.subtype_mk _
    refine ⟨C.comap i hi, ?_, hxC⟩
    have hset : ((C.comap i hi : OpenSubgroup (F r)) : Set (F r)) =
        Subtype.val ⁻¹' (Subtype.val '' (C : Set (F 0))) := by
      ext y
      constructor
      · intro hy
        exact ⟨i y, hy, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have he : i y = z := Subtype.ext hzy.symm
        change i y ∈ C
        rwa [he]
    rw [hset]
    exact (hclosed r hr).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.image continuous_subtype_val)
  let α (r : ℕ) (hr : r ≤ N) := normalizerConj (F r) ⟨g, hg r hr⟩
  have claim : ∀ j r (hrj : r + j = N) (ν : Measure (F r)), ν.IsHaarMeasure →
      ν.map (twistedConjugationMap (α r (by omega))) = displacementFiltrationFactor D r N • ν := by
    intro j
    induction j with
    | zero =>
      intro r hrj ν hν
      obtain rfl : r = N := by omega
      have hbot : ∀ z ∈ F r, z = (1 : G) := fun z hz => by
        rw [hFN, Subgroup.mem_bot] at hz
        exact hz
      have he : twistedConjugationMap (α r le_rfl) = id := by
        funext x
        exact Subtype.ext ((hbot _ (twistedConjugationMap (α r le_rfl) x).2).trans
          (hbot _ x.2).symm)
      rw [he, Measure.map_id, displacementFiltrationFactor, Finset.Ico_self,
        Finset.prod_empty, one_smul]
    | succ j ih =>
      intro r hrj ν hν
      have hr : r < N := by omega
      have : LocallyCompactSpace (F r) := (hclosed r hr.le).locallyCompactSpace
      have : LocallyCompactSpace (F (r + 1)) := (hclosed (r + 1) hr).locallyCompactSpace
      have : SecondCountableTopology (F r) :=
        (hclosed r hr.le).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
      let K := (F (r + 1)).subgroupOf (F r)
      have hK : IsClosed (K : Set (F r)) := (hclosed (r + 1) hr).preimage continuous_subtype_val
      have : LocallyCompactSpace K := hK.locallyCompactSpace
      have : SecondCountableTopology K :=
        hK.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
      let νK : Measure K := haar
      have hqK : ∀ x, q r x = 0 ↔ x ∈ K := hqker r hr
      have hq1 : q r 1 = 0 := (hqK 1).2 K.one_mem
      have hqinv (x : F r) : q r x⁻¹ = -q r x := by
        apply eq_neg_of_add_eq_zero_left
        rw [← hqmul r hr, inv_mul_cancel, hq1]
      have : K.Normal := ⟨fun x hx y => by
        rw [← hqK] at hx ⊢
        rw [hqmul r hr, hqmul r hr, hqinv, hx, add_zero, add_neg_cancel]⟩
      have hα : ∀ x : F r, α r hr.le x ∈ K ↔ x ∈ K := fun x =>
        Subgroup.mem_normalizer_iff.mp (hg (r + 1) hr) x |>.symm
      let e := subgroupOfContinuousMulEquiv (hFle r hr)
      let c := displacementFiltrationFactor D (r + 1) N
      have hpush : (νK.map e).IsHaarMeasure := e.isHaarMeasure_map νK
      have hN : νK.map (twistedConjugationMap (subgroupAutomorphism K (α r hr.le) hα)) = c • νK :=
        map_displacement_of_equiv e (subgroupAutomorphism K (α r hr.le) hα) (α (r + 1) hr)
          (fun x => Subtype.ext rfl) νK c (ih (r + 1) (by omega) (νK.map e) hpush)
      obtain ⟨hGu, hKu⟩ := Langlands.Haar.compactOpenCoverUnimodularity (hcoverF r hr.le)
      have := hGu ν
      have := hKu K hK νK
      have hstep := map_twistedConjugationMap_of_vectorQuotient (hcoverF r hr.le)
        K hK ν νK (α r hr.le) hα (q r) (hqmul r hr) hqK (hqc r hr) (hqo r hr) (hqs r hr)
        (D r) (hqD r hr) c hN
      rw [displacementFiltrationFactor, Finset.prod_eq_prod_Ico_succ_bot hr]
      exact hstep.trans (congrArg (· • ν) (mul_comm _ _))
  exact claim N 0 (by omega) μ inferInstance

end Langlands.HaarModulus.VectorFiltration
