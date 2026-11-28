import Langlands.TraceFormula.NormOneFinitePlaceOrbital
import Langlands.Analysis.Local.QuotientCompatibleScaling
import Langlands.Analysis.Local.QuotientMass

/-!
# Nonvanishing of norm-one orbital integrals of tensors with three prescribed local factors

See `NormOneThreePlaceOrbital.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal CompactlySupported

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration AdelicGroupAutomorphism

universe u

section Scaling

variable {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Orbital integrals for two compatible choices of measures on the same orbit quotient vanish
together. -/
theorem twistedOrbitalIntegral_ne_zero_iff_of_isCompatible (θ : Y →* Y) (hθ : Continuous θ)
    (δ : Y) [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ δ))] (μY : Measure Y)
    {μC μC' : Measure (twistedCentralizer θ δ)}
    [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    [μC'.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC'] [μC'.IsOpenPosMeasure]
    {ν ν' : Measure (LeftQuotient (twistedCentralizer θ δ))}
    (h : IsCompatible (twistedCentralizer θ δ) μY μC ν)
    (h' : IsCompatible (twistedCentralizer θ δ) μY μC' ν') (f : Y → ℂ) :
    twistedOrbitalIntegral θ δ ν f ≠ 0 ↔ twistedOrbitalIntegral θ δ ν' f ≠ 0 := by
  have hC : IsClosed (twistedCentralizer θ δ : Set Y) :=
    isClosed_twistedCentralizer θ hθ δ
  let : LocallyCompactSpace (twistedCentralizer θ δ) := hC.locallyCompactSpace
  let : SecondCountableTopology (twistedCentralizer θ δ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c, hc0, hc⟩ := exists_eq_smul_of_isMulRightInvariant μC μC'
  have hν : c • ν' = (1 : ℝ≥0) • ν := h.smul_eq_smul hC h' (one_smul _ _).symm hc
  rw [one_smul] at hν
  rw [← hν, twistedOrbitalIntegral_smul_measure]
  constructor
  · intro hne h0
    exact hne (by rw [h0, smul_zero])
  · intro hne h0
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact hc0 (by exact_mod_cast h1)
    · exact hne h1

/-- An orbital integral of a continuous function with nonnegative real part, positive at the
base point, is nonzero for every compatible quotient measure, provided the orbit function is
integrable. -/
theorem twistedOrbitalIntegral_ne_zero_of_re_nonneg {Z : Type*} [Group Z] [TopologicalSpace Z]
    [IsTopologicalGroup Z] [MeasurableSpace Z] (θ : Z →* Z) (δ : Z)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
    [MeasurableSpace (twistedCentralizer θ δ)] [MeasurableMul (twistedCentralizer θ δ)]
    (μZ : Measure Z) (μC : Measure (twistedCentralizer θ δ)) [μC.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μZ μC ν) (φ : Z → ℂ) (hφ : Continuous φ)
    (hθ : Continuous θ) (hnn : ∀ z, 0 ≤ (φ z).re) (hpos : 0 < (φ δ).re)
    (hint : Integrable (twistedOrbitFunction θ δ φ) ν) :
    twistedOrbitalIntegral θ δ ν φ ≠ 0 := by
  have := hν.isOpenPosMeasure
  let g : LeftQuotient (twistedCentralizer θ δ) → ℝ := fun q => (twistedOrbitFunction θ δ φ q).re
  have hcont : Continuous (twistedOrbitFunction θ δ φ) := by
    apply continuous_quot_lift
    exact hφ.comp ((continuous_inv.mul continuous_const).mul hθ)
  have hg : Continuous g := Complex.continuous_re.comp hcont
  have hg0 : 0 ≤ g := fun q => by
    induction q using Quotient.inductionOn with
    | h x => exact hnn _
  have hg1 : 0 < g (Quotient.mk _ 1) := by
    change 0 < (φ (1⁻¹ * δ * θ 1)).re
    simpa only [inv_one, one_mul, map_one, mul_one] using hpos
  have hgint : Integrable g ν := hint.re
  have hpos' : 0 < ∫ q, g q ∂ν := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgint]
    have hsub : {q | 0 < g q} ⊆ Function.support g := fun q hq => (ne_of_gt hq)
    exact lt_of_lt_of_le ((isOpen_lt continuous_const hg).measure_pos ν ⟨_, hg1⟩)
      (measure_mono hsub)
  intro h0
  have hre : (twistedOrbitalIntegral θ δ ν φ).re = ∫ q, g q ∂ν := by
    unfold twistedOrbitalIntegral
    exact (integral_re hint).symm
  rw [h0, Complex.zero_re] at hre
  linarith

end Scaling

section NormOne

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

local notation "H" => normOneSubgroup K G

attribute [local instance high] BaseChange.leftQuotientMeasurableSpace
attribute [local instance] BaseChange.leftQuotient_borelSpace

/-- The identity automorphism of `G` gives the identity twist. -/
abbrev normOneOne : H →* H := (normOneAut K (1 : Aut G)).toMonoidHom

/-- The local twist of the identity automorphism at a place. -/
abbrev placeOne (v : Langlands.Global.FinitePlace K) :
    PlaceGroupPoints K G (.inr v) →* PlaceGroupPoints K G (.inr v) :=
  G.affinePointsTarget (1 : Aut G).asIso.hom (placeCompletion K (.inr v))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The identity automorphism gives the identity twist of the norm-one group. -/
theorem normOneOne_eq_id : normOneOne K G = MonoidHom.id H := by
  refine MonoidHom.ext fun x => Subtype.ext ?_
  change map K G G (1 : Aut G).asIso.hom (x : AdelicGroupPoints K G) = (x : AdelicGroupPoints K G)
  exact AdelicGroupAutomorphism.map_id_apply K (x : AdelicGroupPoints K G)

set_option maxHeartbeats 1600000 in
/-- **One finite-place factor.** For the identity automorphism, the norm-one orbital integral
of the positive average of `x ↦ fv(x_v) fw(x)` is, for one compatible quotient measure `ν`,
the local orbital integral of `fv` times a functional of `fw`. -/
theorem normOneFinitePlaceOrbital_one (v : Langlands.Global.FinitePlace K)
    [MeasurableSpace (PlaceGroupPoints K G (.inr v))] [BorelSpace (PlaceGroupPoints K G (.inr v))]
    [(Measure.haar : Measure H).IsMulRightInvariant] (δ : H)
    (hcomm : ∀ x y : twistedCentralizer (normOneOne K G) δ, x * y = y * x)
    (μv : Measure (PlaceGroupPoints K G (.inr v))) [hμv : μv.IsHaarMeasure]
    (μCv : Measure (twistedCentralizer (placeOne K G v) (normOneFinitePlaceProjection K G v δ)))
    [h₁ : μCv.IsMulRightInvariant] [h₂ : IsFiniteMeasureOnCompacts μCv]
    [h₃ : μCv.IsOpenPosMeasure]
    (νv : Measure (LeftQuotient (twistedCentralizer (placeOne K G v)
      (normOneFinitePlaceProjection K G v δ))))
    (hνv : IsCompatible _ μv μCv νv) :
    ∃ (μC : Measure (twistedCentralizer (normOneOne K G) δ))
      (ν : Measure (LeftQuotient (twistedCentralizer (normOneOne K G) δ))),
      IsFiniteMeasureOnCompacts μC ∧ μC.IsOpenPosMeasure ∧
      ∃ hR : μC.IsMulRightInvariant, letI := hR
      IsCompatible _ (Measure.haar : Measure H) μC ν ∧
      ∃ E : (AdelicGroupPoints K G → ℂ) → ℂ,
        ∀ (fv : PlaceGroupPoints K G (.inr v) → ℂ) (fw : AdelicGroupPoints K G → ℂ),
          (∀ z x, fw (z * finitePlacePointInclusion K G v x) = fw z) →
          twistedOrbitalIntegral (normOneOne K G) δ ν
              (normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc)
                (fun x => fv (atPlace K G (.inr v) x) * fw x)) =
            twistedOrbitalIntegral (placeOne K G v) (normOneFinitePlaceProjection K G v δ) νv fv *
              E fw := by
  have key := normOneFinitePlaceOrbital K G v T i hi I e hc
  obtain ⟨νj, μC, ν, -, -, -, hfin, hopen, hR, hcompat, hfac⟩ :=
    @key (1 : Aut G) (by simp) δ hcomm inferInstance inferInstance inferInstance inferInstance
      μv hμv μCv h₁ h₂ h₃ νv hνv
  exact ⟨μC, ν, hfin, hopen, hR, hcompat, _, fun fv fw hfw => hfac fv fw hfw⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [(characterRestrict i).range.FiniteIndex] in
/-- The positive average of a function with nonnegative real part has nonnegative real part. -/
theorem normOnePositiveAverage_re_nonneg (ρ : Measure (intrinsicSubgroup K T))
    (f : AdelicGroupPoints K G → ℂ) (hnn : ∀ g, 0 ≤ (f g).re) (x : H) :
    0 ≤ (normOnePositiveAverage K G T i ρ f x).re := by
  unfold normOnePositiveAverage
  by_cases h : Integrable (fun a => f (positivePointMap K G T i a * (x : AdelicGroupPoints K G))) ρ
  · have h' := integral_re h
    simp only [RCLike.re_to_complex] at h'
    rw [← h']
    exact integral_nonneg fun a => hnn _
  · rw [integral_undef h, Complex.zero_re]

/-- The positive average of a nonnegative compactly supported continuous function that is
positive at a norm-one point is positive there. -/
theorem normOnePositiveAverage_re_pos (f : C_c(AdelicGroupPoints K G, ℂ))
    (hnn : ∀ g, 0 ≤ (f g).re) (x : H) (hx : 0 < (f (x : AdelicGroupPoints K G)).re) :
    0 < (normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc) f x).re := by
  let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
  let : ρ.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure K G T i hi I e hc
  let d := normOneDecomposition K G T i hi I e
  let k : intrinsicSubgroup K T → ℂ := fun a => f (positivePointMap K G T i a * (x : AdelicGroupPoints K G))
  have hkc : Continuous k :=
    f.continuous.comp ((positivePointMap K G T i).continuous.mul continuous_const)
  have hfd : HasCompactSupport (fun p => f (d p)) := f.hasCompactSupport.comp_homeomorph d
  have hks : HasCompactSupport k := by
    have hsub : tsupport k ⊆ Prod.fst '' tsupport (fun p => f (d p)) := by
      have h1 : tsupport k ⊆ (fun a => (a, x)) ⁻¹' tsupport (fun p => f (d p)) :=
        closure_minimal (fun a ha => subset_tsupport _ ha)
          ((isClosed_tsupport _).preimage (continuous_id.prodMk continuous_const))
      exact fun a ha => ⟨(a, x), h1 ha, rfl⟩
    exact (hfd.image continuous_fst).of_isClosed_subset (isClosed_tsupport k) hsub
  have hkint : Integrable k ρ := hkc.integrable_of_hasCompactSupport hks
  unfold normOnePositiveAverage
  change 0 < (∫ a, k a ∂ρ).re
  have h' := integral_re hkint
  simp only [RCLike.re_to_complex] at h'
  rw [← h']
  have hg : Continuous fun a => (k a).re := Complex.continuous_re.comp hkc
  have hg0 : 0 ≤ fun a => (k a).re := fun a => hnn _
  rw [integral_pos_iff_support_of_nonneg hg0 hkint.re]
  have h1 : 0 < (k 1).re := by
    change 0 < (f (positivePointMap K G T i 1 * (x : AdelicGroupPoints K G))).re
    rwa [map_one, one_mul]
  have hsub : {a | 0 < (k a).re} ⊆ Function.support fun a => (k a).re := fun a ha => ne_of_gt ha
  exact lt_of_lt_of_le ((isOpen_lt continuous_const hg).measure_pos ρ ⟨1, h1⟩) (measure_mono hsub)

/-- The local data at one point `x` of the local group: compatible local measures for which the
local orbital integral of `t` at `x` is nonzero. -/
def LocalOrbitalNonvanishingAt (v : Langlands.Global.FinitePlace K)
    [MeasurableSpace (PlaceGroupPoints K G (.inr v))] [BorelSpace (PlaceGroupPoints K G (.inr v))]
    (x : PlaceGroupPoints K G (.inr v)) (t : PlaceGroupPoints K G (.inr v) → ℂ) : Prop :=
  ∃ (μv : Measure (PlaceGroupPoints K G (.inr v))) (_ : μv.IsHaarMeasure)
    (μCv : Measure (twistedCentralizer (placeOne K G v) x))
    (_ : μCv.IsMulRightInvariant) (_ : IsFiniteMeasureOnCompacts μCv) (_ : μCv.IsOpenPosMeasure)
    (νv : Measure (LeftQuotient (twistedCentralizer (placeOne K G v) x))),
    IsCompatible _ μv μCv νv ∧ twistedOrbitalIntegral (placeOne K G v) x νv t ≠ 0

/-- The tensor with three prescribed finite factors and an exterior function. -/
def threePlaceTensor (v₀ v₁ v₂ : Langlands.Global.FinitePlace K)
    (s₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (s₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
    (s₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) (w : AdelicGroupPoints K G → ℂ)
    (x : AdelicGroupPoints K G) : ℂ :=
  s₀ (atPlace K G (.inr v₀) x) * (s₁ (atPlace K G (.inr v₁) x) *
    (s₂ (atPlace K G (.inr v₂) x) * w x))

omit [LocallyOfFiniteType G.X.hom] in
theorem atPlace_mul_finitePlacePointInclusion_of_ne {v w : Langlands.Global.FinitePlace K}
    (h : w ≠ v) (z : AdelicGroupPoints K G) (x : PlaceGroupPoints K G (.inr v)) :
    atPlace K G (.inr w) (z * finitePlacePointInclusion K G v x) = atPlace K G (.inr w) z := by
  rw [map_mul, atPlace_finitePlacePointInclusion_of_ne K G v (.inr w)
    (fun h' => h (Sum.inr.inj h')), mul_one]

set_option maxHeartbeats 3200000 in
/-- **Nonvanishing for three prescribed local factors.** Let `t₀, t₁, t₂` be local functions at
three distinct finite places whose local orbital integrals at `δ` are nonzero for some
compatible local measures, and let `b₀, b₁, b₂` be local functions with a nonvanishing
norm-one orbital integral of the tensor `b₀ ⊗ b₁ ⊗ b₂ ⊗ w`. Then the norm-one orbital integral of
the positive average of `t₀ ⊗ t₁ ⊗ t₂ ⊗ w` at `δ` is nonzero for every compatible choice of
measures. Each step factors out one place with `normOneFinitePlaceOrbital`. -/
theorem threePlaceTensor_orbitalIntegral_ne_zero
    [∀ v : Langlands.Global.FinitePlace K, MeasurableSpace (PlaceGroupPoints K G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace K, BorelSpace (PlaceGroupPoints K G (.inr v))]
    [(Measure.haar : Measure H).IsMulRightInvariant]
    (v₀ v₁ v₂ : Langlands.Global.FinitePlace K) (h01 : v₀ ≠ v₁) (h02 : v₀ ≠ v₂)
    (h12 : v₁ ≠ v₂) (δ : H) (θ : H →* H) (hθ : θ = MonoidHom.id H)
    (hcomm : ∀ x y : twistedCentralizer θ δ, x * y = y * x)
    (t₀ b₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (t₁ b₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
    (t₂ b₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) (w : AdelicGroupPoints K G → ℂ)
    (hw₀ : ∀ z x, w (z * finitePlacePointInclusion K G v₀ x) = w z)
    (hw₁ : ∀ z x, w (z * finitePlacePointInclusion K G v₁ x) = w z)
    (hw₂ : ∀ z x, w (z * finitePlacePointInclusion K G v₂ x) = w z)
    (hloc₀ : LocalOrbitalNonvanishingAt K G v₀
      (normOneFinitePlaceProjection K G v₀ δ) t₀)
    (hloc₁ : LocalOrbitalNonvanishingAt K G v₁
      (normOneFinitePlaceProjection K G v₁ δ) t₁)
    (hloc₂ : LocalOrbitalNonvanishingAt K G v₂
      (normOneFinitePlaceProjection K G v₂ δ) t₂)
    (hpos : ∀ (μC : Measure (twistedCentralizer (θ) δ)) [μC.IsMulRightInvariant]
      [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (ν : Measure (LeftQuotient (twistedCentralizer (θ) δ))),
      IsCompatible _ (Measure.haar : Measure H) μC ν →
      twistedOrbitalIntegral (θ) δ ν
        (normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc)
          (threePlaceTensor K G v₀ v₁ v₂ b₀ b₁ b₂ w)) ≠ 0)
    (μC : Measure (twistedCentralizer (θ) δ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (ν : Measure (LeftQuotient (twistedCentralizer (θ) δ)))
    (hν : IsCompatible _ (Measure.haar : Measure H) μC ν) :
    twistedOrbitalIntegral (θ) δ ν
      (normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc)
        (threePlaceTensor K G v₀ v₁ v₂ t₀ t₁ t₂ w)) ≠ 0 := by
  rw [← normOneOne_eq_id K G] at hθ
  subst hθ
  have hθ : Continuous (normOneOne K G) := (normOneAut K (1 : Aut G)).continuous
  let ρ := normalizedPositiveHaarMeasure K G T i hi I e hc
  let O (ν' : Measure (LeftQuotient (twistedCentralizer (normOneOne K G) δ)))
      (s₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (s₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
      (s₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) : ℂ :=
    twistedOrbitalIntegral (normOneOne K G) δ ν'
      (normOnePositiveAverage K G T i ρ (threePlaceTensor K G v₀ v₁ v₂ s₀ s₁ s₂ w))
  change O ν t₀ t₁ t₂ ≠ 0
  -- the place `v₀`
  obtain ⟨μv₀, _, μCv₀, _, _, _, νv₀, hνv₀, hO₀⟩ := hloc₀
  obtain ⟨μC₀, ν₀, _, _, hR₀, hc₀, E₀, hE₀⟩ :=
    normOneFinitePlaceOrbital_one K G T i hi I e hc v₀ δ hcomm μv₀ μCv₀ νv₀ hνv₀
  let := hR₀
  have hF₀ (s₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (s₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
      (s₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) :
      O ν₀ s₀ s₁ s₂ = twistedOrbitalIntegral (placeOne K G v₀)
        (normOneFinitePlaceProjection K G v₀ δ) νv₀ s₀ *
        E₀ (fun x => s₁ (atPlace K G (.inr v₁) x) * (s₂ (atPlace K G (.inr v₂) x) * w x)) := by
    apply hE₀
    intro z x
    rw [atPlace_mul_finitePlacePointInclusion_of_ne K G (Ne.symm h01),
      atPlace_mul_finitePlacePointInclusion_of_ne K G (Ne.symm h02), hw₀]
  have hb₀ : O ν₀ b₀ b₁ b₂ ≠ 0 := hpos μC₀ ν₀ hc₀
  have hA : O ν₀ t₀ b₁ b₂ ≠ 0 := by
    rw [hF₀] at hb₀ ⊢
    exact mul_ne_zero hO₀ (right_ne_zero_of_mul hb₀)
  -- the place `v₁`
  obtain ⟨μv₁, _, μCv₁, _, _, _, νv₁, hνv₁, hO₁⟩ := hloc₁
  obtain ⟨μC₁, ν₁, _, _, hR₁, hc₁, E₁, hE₁⟩ :=
    normOneFinitePlaceOrbital_one K G T i hi I e hc v₁ δ hcomm μv₁ μCv₁ νv₁ hνv₁
  let := hR₁
  have hF₁ (s₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (s₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
      (s₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) :
      O ν₁ s₀ s₁ s₂ = twistedOrbitalIntegral (placeOne K G v₁)
        (normOneFinitePlaceProjection K G v₁ δ) νv₁ s₁ *
        E₁ (fun x => s₀ (atPlace K G (.inr v₀) x) * (s₂ (atPlace K G (.inr v₂) x) * w x)) := by
    have h : threePlaceTensor K G v₀ v₁ v₂ s₀ s₁ s₂ w = fun x => s₁ (atPlace K G (.inr v₁) x) *
        (s₀ (atPlace K G (.inr v₀) x) * (s₂ (atPlace K G (.inr v₂) x) * w x)) := by
      funext x
      simp only [threePlaceTensor]
      ring
    change twistedOrbitalIntegral (normOneOne K G) δ ν₁
      (normOnePositiveAverage K G T i ρ (threePlaceTensor K G v₀ v₁ v₂ s₀ s₁ s₂ w)) = _
    rw [h]
    apply hE₁
    intro z x
    rw [atPlace_mul_finitePlacePointInclusion_of_ne K G h01,
      atPlace_mul_finitePlacePointInclusion_of_ne K G (Ne.symm h12), hw₁]
  have hB : O ν₁ t₀ t₁ b₂ ≠ 0 := by
    have h1 : O ν₁ t₀ b₁ b₂ ≠ 0 :=
      (twistedOrbitalIntegral_ne_zero_iff_of_isCompatible _ hθ δ _ hc₀ hc₁ _).mp hA
    rw [hF₁] at h1 ⊢
    exact mul_ne_zero hO₁ (right_ne_zero_of_mul h1)
  -- the place `v₂`
  obtain ⟨μv₂, _, μCv₂, _, _, _, νv₂, hνv₂, hO₂⟩ := hloc₂
  obtain ⟨μC₂, ν₂, _, _, hR₂, hc₂, E₂, hE₂⟩ :=
    normOneFinitePlaceOrbital_one K G T i hi I e hc v₂ δ hcomm μv₂ μCv₂ νv₂ hνv₂
  let := hR₂
  have hF₂ (s₀ : PlaceGroupPoints K G (.inr v₀) → ℂ) (s₁ : PlaceGroupPoints K G (.inr v₁) → ℂ)
      (s₂ : PlaceGroupPoints K G (.inr v₂) → ℂ) :
      O ν₂ s₀ s₁ s₂ = twistedOrbitalIntegral (placeOne K G v₂)
        (normOneFinitePlaceProjection K G v₂ δ) νv₂ s₂ *
        E₂ (fun x => s₀ (atPlace K G (.inr v₀) x) * (s₁ (atPlace K G (.inr v₁) x) * w x)) := by
    have h : threePlaceTensor K G v₀ v₁ v₂ s₀ s₁ s₂ w = fun x => s₂ (atPlace K G (.inr v₂) x) *
        (s₀ (atPlace K G (.inr v₀) x) * (s₁ (atPlace K G (.inr v₁) x) * w x)) := by
      funext x
      simp only [threePlaceTensor]
      ring
    change twistedOrbitalIntegral (normOneOne K G) δ ν₂
      (normOnePositiveAverage K G T i ρ (threePlaceTensor K G v₀ v₁ v₂ s₀ s₁ s₂ w)) = _
    rw [h]
    apply hE₂
    intro z x
    rw [atPlace_mul_finitePlacePointInclusion_of_ne K G h02,
      atPlace_mul_finitePlacePointInclusion_of_ne K G h12, hw₂]
  have hC : O ν₂ t₀ t₁ t₂ ≠ 0 := by
    have h1 : O ν₂ t₀ t₁ b₂ ≠ 0 :=
      (twistedOrbitalIntegral_ne_zero_iff_of_isCompatible _ hθ δ _ hc₁ hc₂ _).mp hB
    rw [hF₂] at h1 ⊢
    exact mul_ne_zero hO₂ (right_ne_zero_of_mul h1)
  exact (twistedOrbitalIntegral_ne_zero_iff_of_isCompatible _ hθ δ _ hc₂ hν _).mp hC

end NormOne

end Langlands.TraceFormula
