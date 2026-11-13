import Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Compatible Haar measures for Renard VII.3.5 (i) from the product decomposition

`PQCompositionHaarStatement` (clause 1 of `PQIntertwiningCompositionStatement`) follows from the
product decomposition `PQCompositionProductStatement` (multiplication `V₁₂ × V₂₃ → V₁₃` is a
homeomorphism): the Haar measure on `V₁₃` is the image of the product of the Haar measures on
`V₁₂` and `V₂₃`. The groups `V₂₃` and `V₁₃` lie in `N₃(F)`, which is a limit of compact
subgroups, so they are unimodular; this is what makes the image measure left invariant.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Measure Topology
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

section CompositionHaar

/-- A Haar measure on a second countable locally compact group in which every compact set lies
in a compact subgroup is right invariant. -/
theorem isMulRightInvariant_of_forall_isCompact_subgroup {X : Type*} [Group X]
    [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (m : Measure X) [m.IsHaarMeasure]
    (h : ∀ C : Set X, IsCompact C → ∃ K : Subgroup X, IsCompact (K : Set X) ∧ C ⊆ K) :
    m.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : X)
  obtain ⟨K, hK, hCK⟩ := h (insert g C) (hC.insert g)
  have hKn : (K : Set X) ∈ 𝓝 (1 : X) :=
    Filter.mem_of_superset hC1 fun x hx => hCK (Set.mem_insert_of_mem g hx)
  have hgK : g ∈ K := hCK (Set.mem_insert g C)
  have hpos : m K ≠ 0 := (measure_pos_of_mem_nhds m hKn).ne'
  have hfin : m K ≠ ∞ := hK.measure_lt_top.ne
  have hKm : MeasurableSet (K : Set X) := hK.isClosed.measurableSet
  have hpre : (fun x => x * g) ⁻¹' (K : Set X) = K := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hx => by simpa using K.mul_mem hx (K.inv_mem hgK), fun hx => K.mul_mem hx hgK⟩
  have hC : map (· * g) m = haarScalarFactor (map (· * g) m) m • m :=
    isMulLeftInvariant_eq_smul _ _
  suffices hc : haarScalarFactor (map (· * g) m) m = 1 by rwa [hc, one_smul] at hC
  have : (haarScalarFactor (map (· * g) m) m : ℝ≥0∞) * m K = 1 * m K := by
    rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← Measure.smul_apply, ← hC,
      map_apply (measurable_mul_const g) hKm, hpre]
  rwa [ENNReal.mul_left_inj hpos hfin, ENNReal.coe_eq_one] at this

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V₁₂ V₂₃ V₁₃ : Subgroup H}

omit [IsTopologicalGroup H] in
/-- A closed subgroup of a second countable, locally compact, Hausdorff group is
σ-compact. -/
theorem sigmaCompactSpace_of_isClosed_subgroup [SecondCountableTopology H]
    [LocallyCompactSpace H] {V : Subgroup H} (hV : IsClosed (V : Set H)) :
    SigmaCompactSpace V := by
  have : LocallyCompactSpace V := hV.locallyCompactSpace
  have : SecondCountableTopology V :=
    TopologicalSpace.Subtype.secondCountableTopology (V : Set H)
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

omit [IsTopologicalGroup H] in
/-- A closed subgroup `V` of a limit of compact subgroups `U` is again a limit of compact
subgroups: every compact subset of `V` lies in a compact subgroup of `V`. -/
theorem forall_isCompact_subgroup_of_le {U V : Subgroup H}
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) (hVU : V ≤ U)
    (hV : IsClosed (V : Set H)) :
    ∀ C : Set V, IsCompact C → ∃ K : Subgroup V, IsCompact (K : Set V) ∧ C ⊆ K := by
  intro C hC
  let incl : V →* U := Subgroup.inclusion hVU
  have hι : Continuous incl := continuous_inclusion hVU
  obtain ⟨K, hK, hCK⟩ := hU (incl '' C) (hC.image hι)
  refine ⟨K.comap incl, ?_, fun x hx => hCK ⟨x, hx, rfl⟩⟩
  have hset : ((K.comap incl : Subgroup V) : Set V) =
      (Subtype.val : V → H) ⁻¹' ((Subtype.val : U → H) '' (K : Set U)) := by
    ext x
    simp only [Subgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hx
      exact ⟨incl x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = incl x := Subtype.ext hyx
      rwa [← this]
  rw [hset]
  exact hV.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.image continuous_subtype_val)

/-- The image of the product of two Haar measures under a multiplication homeomorphism
`V₁₂ × V₂₃ ≃ₜ V₁₃` is a Haar measure on `V₁₃` when every compact subset of `V₂₃`, and of `V₁₃`,
lies in a compact subgroup. It computes integrals of continuous compactly supported functions
on the ambient group by the iterated integral over `V₂₃` and `V₁₂`. -/
theorem exists_compatible_haar_of_mul_homeomorph
    [T2Space H] [SecondCountableTopology H] [LocallyCompactSpace H]
    (h₁₂ : IsClosed (V₁₂ : Set H)) (h₂₃ : IsClosed (V₂₃ : Set H))
    (h₁₃ : IsClosed (V₁₃ : Set H))
    (hc₂₃ : ∀ C : Set V₂₃, IsCompact C → ∃ K : Subgroup V₂₃, IsCompact (K : Set V₂₃) ∧ C ⊆ K)
    (hc₁₃ : ∀ C : Set V₁₃, IsCompact C → ∃ K : Subgroup V₁₃, IsCompact (K : Set V₁₃) ∧ C ⊆ K)
    (e : V₁₂ × V₂₃ ≃ₜ V₁₃) (he : ∀ x, (e x : H) = (x.1 : H) * x.2)
    [MeasurableSpace V₁₂] [BorelSpace V₁₂] [MeasurableSpace V₂₃] [BorelSpace V₂₃]
    [MeasurableSpace V₁₃] [BorelSpace V₁₃]
    (μ₁₂ : Measure V₁₂) (μ₂₃ : Measure V₂₃) [μ₁₂.IsHaarMeasure] [μ₂₃.IsHaarMeasure] :
    ∃ μ₁₃ : Measure V₁₃, μ₁₃.IsHaarMeasure ∧
      ∀ φ : H → ℂ, Continuous φ → HasCompactSupport φ →
        ∫ x : V₁₃, φ x ∂μ₁₃ = ∫ u : V₂₃, ∫ w : V₁₂, φ ((w : H) * u) ∂μ₁₂ ∂μ₂₃ := by
  have : SigmaCompactSpace V₁₂ := sigmaCompactSpace_of_isClosed_subgroup h₁₂
  have : SigmaCompactSpace V₂₃ := sigmaCompactSpace_of_isClosed_subgroup h₂₃
  have : LocallyCompactSpace V₁₂ := h₁₂.locallyCompactSpace
  have : LocallyCompactSpace V₂₃ := h₂₃.locallyCompactSpace
  have : LocallyCompactSpace V₁₃ := h₁₃.locallyCompactSpace
  have : SecondCountableTopology V₁₂ :=
    TopologicalSpace.Subtype.secondCountableTopology (V₁₂ : Set H)
  have : SecondCountableTopology V₂₃ :=
    TopologicalSpace.Subtype.secondCountableTopology (V₂₃ : Set H)
  have : SecondCountableTopology V₁₃ :=
    TopologicalSpace.Subtype.secondCountableTopology (V₁₃ : Set H)
  have : BorelSpace (V₁₂ × V₂₃) := Prod.borelSpace
  let ν : Measure (V₁₂ × V₂₃) := μ₁₂.prod μ₂₃
  let μ₁₃ : Measure V₁₃ := ν.map e
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  -- unimodularity of `V₂₃` and `V₁₃`
  have : μ₂₃.IsMulRightInvariant := isMulRightInvariant_of_forall_isCompact_subgroup μ₂₃ hc₂₃
  let m : Measure V₁₃ := Measure.haar
  have : m.IsMulRightInvariant := isMulRightInvariant_of_forall_isCompact_subgroup m hc₁₃
  -- the coordinates `g = w u ↦ (w, u⁻¹)` turn the two-sided action into left translation
  let ψ : V₁₂ × V₂₃ ≃ₜ V₁₂ × V₂₃ := (Homeomorph.refl V₁₂).prodCongr (Homeomorph.inv V₂₃)
  let f : V₁₃ ≃ₜ V₁₂ × V₂₃ := e.symm.trans ψ
  let i₁ : V₁₂ → V₁₃ := fun w => e (w, 1)
  let i₂ : V₂₃ → V₁₃ := fun u => e (1, u)
  have hψ : ∀ p : V₁₂ × V₂₃, ψ p = (p.1, p.2⁻¹) := fun p => by
    simp [ψ, Homeomorph.coe_prodCongr, Prod.map]
  have hfe' : ∀ p : V₁₂ × V₂₃, f (e p) = (p.1, p.2⁻¹) := fun p => by
    simp only [f, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hψ]
  have hf : ∀ (x : V₁₂ × V₂₃) (g : V₁₃), f (i₁ x.1 * g * (i₂ x.2)⁻¹) = x * f g := by
    intro x g
    obtain ⟨⟨w, u⟩, rfl⟩ := e.surjective g
    have hg : i₁ x.1 * e (w, u) * (i₂ x.2)⁻¹ = e (x.1 * w, u * x.2⁻¹) := by
      apply Subtype.ext
      simp only [i₁, i₂, Subgroup.coe_mul, Subgroup.coe_inv, he, OneMemClass.coe_one, mul_one,
        one_mul, mul_assoc]
    rw [hg, hfe', hfe']
    ext <;> simp [mul_inv_rev]
  have hleftμ : (m.map f).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    rw [map_map (measurable_const_mul x) f.measurable]
    have hcomp : (fun y => x * y) ∘ f =
        f ∘ ((fun g => g * (i₂ x.2)⁻¹) ∘ fun g => i₁ x.1 * g) := by
      funext g
      simp only [Function.comp_apply, ← hf, mul_assoc]
    rw [hcomp, ← map_map f.measurable ((measurable_mul_const _).comp (measurable_const_mul _)),
      ← map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]
  have hleftν : (ν.map ψ).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    rw [map_map (measurable_const_mul x) ψ.measurable]
    have hcomp : (fun y => x * y) ∘ ψ =
        ψ ∘ Prod.map (fun w => x.1 * w) (fun u => u * x.2⁻¹) := by
      funext y
      simp only [Function.comp_apply, hψ]
      ext <;> simp [mul_inv_rev]
    rw [hcomp, ← map_map ψ.measurable
        ((measurable_const_mul _).prodMap (measurable_mul_const _)),
      ← map_prod_map μ₁₂ μ₂₃ (measurable_const_mul _) (measurable_mul_const _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have : IsFiniteMeasureOnCompacts (m.map f) := IsFiniteMeasureOnCompacts.map m f
  have : (m.map f).IsOpenPosMeasure := f.continuous.isOpenPosMeasure_map f.surjective
  have : (m.map f).IsHaarMeasure := ⟨⟩
  have : IsFiniteMeasureOnCompacts (ν.map ψ) := IsFiniteMeasureOnCompacts.map ν ψ
  have : (ν.map ψ).IsOpenPosMeasure := ψ.continuous.isOpenPosMeasure_map ψ.surjective
  have : (ν.map ψ).IsHaarMeasure := ⟨⟩
  set c : ℝ≥0 := haarScalarFactor (m.map f) (ν.map ψ) with hc_def
  have hc : m.map f = c • ν.map ψ := isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hμ : m = c • μ₁₃ := by
    have hback : m = (m.map f).map f.symm := by
      rw [map_map f.symm.measurable f.measurable, f.symm_comp_self, map_id]
    have hfe : (f.symm : V₁₂ × V₂₃ → V₁₃) ∘ ψ = e := by
      funext x
      simp [f]
    rw [hback, hc, Measure.map_smul, map_map f.symm.measurable ψ.measurable, hfe]
    exact f.symm.continuous.measurable.aemeasurable
  have hμ₁₃ : μ₁₃ = c⁻¹ • m := by
    rw [hμ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hleft : μ₁₃.IsMulLeftInvariant := by
    rw [hμ₁₃]
    infer_instance
  have hfin : IsFiniteMeasureOnCompacts μ₁₃ := IsFiniteMeasureOnCompacts.map ν e
  have hpos : μ₁₃.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hhaar : μ₁₃.IsHaarMeasure := ⟨⟩
  refine ⟨μ₁₃, hhaar, ?_⟩
  intro φ hφ hφc
  have hval : IsClosedEmbedding (Subtype.val : V₁₃ → H) := h₁₃.isClosedEmbedding_subtypeVal
  have hcomp : HasCompactSupport (fun x : V₁₂ × V₂₃ => φ ((e x : V₁₃) : H)) :=
    (hφc.comp_isClosedEmbedding hval).comp_isClosedEmbedding e.isClosedEmbedding
  have hcont : Continuous (fun x : V₁₂ × V₂₃ => φ ((e x : V₁₃) : H)) :=
    hφ.comp (continuous_subtype_val.comp e.continuous)
  have hint : Integrable (fun x : V₁₂ × V₂₃ => φ ((e x : V₁₃) : H)) ν :=
    hcont.integrable_of_hasCompactSupport hcomp
  rw [hme.integral_map]
  rw [integral_prod_symm _ hint]
  simp only [he]

end CompositionHaar

open GroupScheme

/-- Clause 1 of Renard VII.3.5 (i) (`PQCompositionHaarStatement`) from the product
decomposition `V₁₃ = V₁₂ V₂₃`. -/
theorem pqCompositionHaar_of_product (hProd : PQCompositionProductStatement.{u}) :
    PQCompositionHaarStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
    V₁₂ V₂₃ V₁₃ _ _ _ _ _ _ Compatible haar₁₂ haar₂₃ h₁₂ h₂₃
  obtain ⟨e, he⟩ := hProd k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have hc₁₂ : IsClosed (V₁₂ : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb₁ rb₁ hpb₁.isClosedSubgroup hrb₁.1.isClosedSubgroup).inter
      (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
  have hc₂₃ : IsClosed (V₂₃ : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb₂ rb₂ hpb₂.isClosedSubgroup hrb₂.1.isClosedSubgroup).inter
      (isClosed_pointImage_comp p₃ r₃ hp₃.isClosedSubgroup hr₃.1.isClosedSubgroup)
  have hc₁₃ : IsClosed (V₁₃ : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb₁ rb₁ hpb₁.isClosedSubgroup hrb₁.1.isClosedSubgroup).inter
      (isClosed_pointImage_comp p₃ r₃ hp₃.isClosedSubgroup hr₃.1.isClosedSubgroup)
  have hN₃ : Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r₃ ≫ p₃)) :=
    isLimitOfCompactSubgroups_pointImage_radical p₃ r₃ hp₃.isClosedSubgroup hr₃.1
  have := h₁₂
  have := h₂₃
  exact exists_compatible_haar_of_mul_homeomorph hc₁₂ hc₂₃ hc₁₃
    (forall_isCompact_subgroup_of_le hN₃ inf_le_right hc₂₃)
    (forall_isCompact_subgroup_of_le hN₃ inf_le_right hc₁₃) e he haar₁₂ haar₂₃

set_option linter.defProp false in
/-- The implication of `pqCompositionHaar_of_product`, recorded as a definition: the product
decomposition implies `PQCompositionHaarStatement`. -/
def pqCompositionHaarOfProduct :
    PQCompositionProductStatement.{u} → PQCompositionHaarStatement.{u} :=
  pqCompositionHaar_of_product

end Langlands.Aubert.General.RepresentedParabolic
