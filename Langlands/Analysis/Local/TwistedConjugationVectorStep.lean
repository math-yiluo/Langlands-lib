import Langlands.Analysis.Local.TwistedConjugationHaar
import Langlands.Analysis.Local.VectorFiltrationHaarModulusProof

/-! # Twisted conjugation across an additive vector quotient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.QuotientIntegration

open Langlands.HaarModulus.VectorFiltration

universe u v

section Coordinates

variable {G : Type u} [Group G] {W : Type v} [AddGroup W]
  (N : Subgroup G) (q : G → W) (hqmul : ∀ x y, q (x * y) = q x + q y)
  (hqker : ∀ x, q x = 0 ↔ x ∈ N)

include hqker in
private theorem vectorQuotient_map_one : q 1 = 0 := by
  exact (hqker 1).2 N.one_mem

include hqmul hqker in
private theorem vectorQuotient_map_inv (g : G) : q g⁻¹ = -q g := by
  apply eq_neg_of_add_eq_zero_left
  rw [← hqmul, inv_mul_cancel, vectorQuotient_map_one N q hqker]

include hqmul hqker in
private theorem vectorQuotient_relation (x y : G) :
    QuotientGroup.rightRel N x y ↔ q x = q y := by
  rw [QuotientGroup.rightRel_apply, ← hqker, hqmul, vectorQuotient_map_inv N q hqmul hqker,
    add_neg_eq_zero]
  exact eq_comm

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace W]

/-- The homeomorphism from the actual left quotient to additive coordinates
provided by a continuous open surjective map with the given kernel. -/
def vectorQuotientHomeomorph (hqc : Continuous q) (hqo : IsOpenMap q)
    (hqs : Function.Surjective q) : LeftQuotient N ≃ₜ W := by
  let f : LeftQuotient N → W := fun q' =>
    Quotient.lift q (fun x y h => (vectorQuotient_relation N q hqmul hqker x y).mp h) q'
  have hf : ∀ x : G, f (leftQuotientMap N x) = q x := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    obtain ⟨y, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((vectorQuotient_relation N q hqmul hqker x y).mpr hxy)
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨x, rfl⟩ := hqs w
    exact ⟨leftQuotientMap N x, hf x⟩
  have hquot := leftQuotient_isOpenQuotientMap N
  have hfc : Continuous f := hquot.isQuotientMap.continuous_iff.mpr hqc
  have hfo : IsOpenMap f := by
    intro S hS
    rw [← Set.image_preimage_eq S hquot.surjective, Set.image_image]
    exact hqo _ (hS.preimage hquot.continuous)
  exact (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hfc hfo

@[simp] theorem vectorQuotientHomeomorph_mk (hqc : Continuous q) (hqo : IsOpenMap q)
    (hqs : Function.Surjective q) (g : G) :
    vectorQuotientHomeomorph N q hqmul hqker hqc hqo hqs (leftQuotientMap N g) = q g := rfl

end Coordinates

section Scaling

variable {k : Type v} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- If the quotient action of `α` is `A`, its displacement on that quotient
is `1 - A`. Multiply the Haar scale of this linear equivalence by the
scale on the kernel. -/
theorem map_twistedConjugationMap_of_vectorQuotient
    (hcover : ∀ g : G, ∃ B : OpenSubgroup G, IsCompact (B : Set G) ∧ g ∈ B)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    [MeasurableSpace N] [BorelSpace N] [LocallyCompactSpace N]
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (μN : Measure N) [SFinite μN] [μN.IsHaarMeasure] [μN.Regular] [μN.IsMulRightInvariant]
    (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ N ↔ x ∈ N)
    {n : ℕ} (q : G → Fin n → k) (hqmul : ∀ x y, q (x * y) = q x + q y)
    (hqker : ∀ x, q x = 0 ↔ x ∈ N) (hqc : Continuous q) (hqo : IsOpenMap q)
    (hqs : Function.Surjective q)
    (D : (Fin n → k) ≃ₗ[k] (Fin n → k)) (hD : ∀ x, D (q x) = q x - q (α x))
    (c : ℝ≥0∞)
    (hmapN : μN.map (twistedConjugationMap (subgroupAutomorphism N α hα)) = c • μN) :
    μG.map (twistedConjugationMap α) =
      (c * ((MeasureTheory.distribHaarChar k (LinearEquiv.det D) : ℝ≥0∞))⁻¹) • μG := by
  let : MeasurableSpace (LeftQuotient N) := borel _
  let : BorelSpace (LeftQuotient N) := ⟨rfl⟩
  let : MeasurableSpace k := borel _
  let : BorelSpace k := ⟨rfl⟩
  let : T2Space k := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space k
  let : SecondCountableTopology k :=
    Langlands.HarmonicAnalysis.GeneralLocalField.secondCountableTopology k
  obtain ⟨ν, hν⟩ := compatibleMeasureExists N hN μG μN
  let e := vectorQuotientHomeomorph N q hqmul hqker hqc hqo hqs
  have he_mk (g : G) : e (leftQuotientMap N g) = q g := rfl
  have he_m : Measurable (e : LeftQuotient N → Fin n → k) := e.continuous.measurable
  have he_sm : Measurable (e.symm : (Fin n → k) → LeftQuotient N) := e.symm.continuous.measurable
  have hDm : Measurable (D : (Fin n → k) → Fin n → k) :=
    (LinearMap.continuous_on_pi (D : (Fin n → k) →ₗ[k] (Fin n → k))).measurable
  let τ (w : LeftQuotient N) := e.symm (D (e w))
  have hτ : Measurable τ := he_sm.comp (hDm.comp he_m)
  have hτ_mk (g : G) : τ (leftQuotientMap N g) = leftQuotientMap N (twistedConjugationMap α g) := by
    apply e.injective
    change e (e.symm (D (e (leftQuotientMap N g)))) = e (leftQuotientMap N ((α g)⁻¹ * g))
    rw [e.apply_symm_apply, he_mk, he_mk, hD, hqmul, vectorQuotient_map_inv N q hqmul hqker]
    abel
  let ρ := ν.map e
  let : ν.Regular := hν.regular
  let : ρ.Regular := Regular.map e
  let : ρ.IsAddLeftInvariant := ⟨fun w => by
    obtain ⟨g, rfl⟩ := hqs w
    have hc : (fun v => q g + v) ∘ e = e ∘ rightTranslate N g := by
      funext v
      obtain ⟨x, rfl⟩ := Quotient.exists_rep v
      change q g + e (leftQuotientMap N x) = e (leftQuotientMap N (x * g))
      rw [he_mk, he_mk, hqmul, add_comm]
    change (ν.map e).map (fun v => q g + v) = ν.map e
    rw [Measure.map_map (measurable_const_add _) he_m, hc,
      ← Measure.map_map he_m (rightTranslate N g).continuous.measurable, (hν.right_invariant g).map_eq]⟩
  let m : Measure (Fin n → k) := addHaar
  let η : Measure k := addHaar
  let cD : ℝ≥0 := (MeasureTheory.distribHaarChar k (LinearEquiv.det D))⁻¹
  have hdet : (LinearMap.toMatrix' (D : (Fin n → k) →ₗ[k] (Fin n → k))).det =
      (LinearEquiv.det D : k) := by rw [LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hmD : m.map D = cD • m := by
    have hd : (LinearMap.toMatrix' (D : (Fin n → k) →ₗ[k] (Fin n → k))).det ≠ 0 := by
      rw [hdet]
      exact (LinearEquiv.det D).ne_zero
    have h := Langlands.HarmonicAnalysis.haarMeasure_map_matrix η (scalingWithZero (k := k))
      (fun a ha => map_mul_left_eq_scalingWithZero η a ha) m hd
    rw [Matrix.toLin'_toMatrix', LinearEquiv.coe_coe, hdet,
      scalingWithZero_of_ne_zero (LinearEquiv.det D).ne_zero] at h
    have hunit : Units.mk0 _ (LinearEquiv.det D).ne_zero = LinearEquiv.det D := Units.ext rfl
    simpa only [hunit] using h
  have hρD : ρ.map D = cD • ρ := by
    have h := isAddLeftInvariant_eq_smul_of_regular ρ m
    conv_lhs => rw [h]
    conv_rhs => rw [h]
    rw [Measure.map_smul _ hDm.aemeasurable, hmD, smul_comm]
  have hνD : ν.map τ = cD • ν := by
    have hc : (e : LeftQuotient N → Fin n → k) ∘ τ = D ∘ e :=
      funext fun x => e.apply_symm_apply (D (e x))
    have h := congrArg (Measure.map e.symm) hρD
    change ((ν.map e).map D).map e.symm = (cD • ν.map e).map e.symm at h
    rw [Measure.map_map hDm he_m, ← hc,
      ← Measure.map_map he_m hτ, Measure.map_map he_sm he_m, Homeomorph.symm_comp_self,
      Measure.map_id, Measure.map_smul _ he_sm.aemeasurable, Measure.map_map he_sm he_m,
      Homeomorph.symm_comp_self, Measure.map_id] at h
    exact h
  have hD0 : MeasureTheory.distribHaarChar k (LinearEquiv.det D) ≠ 0 :=
    ((Group.isUnit (LinearEquiv.det D)).map (MeasureTheory.distribHaarChar k)).ne_zero
  exact map_twistedConjugationMap_of_quotient N hN μG μN ν hν hcover α hα τ hτ hτ_mk
    c _ hmapN (by
      rw [← ENNReal.coe_inv hD0]
      exact hνD)

end Scaling

end Langlands.QuotientIntegration
