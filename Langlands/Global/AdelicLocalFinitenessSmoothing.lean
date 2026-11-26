import Langlands.Global.AdelicWeightedHilbertRealization
import Langlands.Global.AdelicIwasawaChamberBounds
import Langlands.Global.AdelicLocalFinitenessChamberWeights
import Langlands.Global.AdelicGroupRationalTopology

/-! # Smoothing operators on the weighted Siegel Hilbert space

For linear chamber coordinates `e` on the real dual of `P`, the weighted Hilbert space of the
Siegel region `{H | τ_α < (e H)_α for all simple directions α}` with the log weight
`localFinitenessLogWeight ra rb ∘ e` carries continuous linear right convolution operators into a
uniform-growth Fréchet space, computed on every measurable representative, provided the rational
representatives of `G(𝔸)` with polynomially bounded height lie deeper in the region than the
displacement of heights by the supports of the kernels.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions
  AdelicSiegelFactors

/-- The Siegel region of heights `{H | τ_α < (e H)_α for every simple direction α}` for a
coordinate map `e` with root part indexed by `Δ`. -/
def siegelHeightRegion {V Δ : Type*} {r : ℕ} (e : V → (Δ → ℝ) × (Fin r → ℝ)) (τ : Δ → ℝ) :
    Set V :=
  {H | ∀ α, τ α < (e H).1 α}

theorem isOpen_siegelHeightRegion {V Δ : Type*} [TopologicalSpace V] [Finite Δ] {r : ℕ}
    {e : V → (Δ → ℝ) × (Fin r → ℝ)} (he : Continuous e) (τ : Δ → ℝ) :
    IsOpen (siegelHeightRegion e τ) := by
  have : siegelHeightRegion e τ = ⋂ α, {H | τ α < (e H).1 α} := by
    ext H
    simp [siegelHeightRegion]
  rw [this]
  exact isOpen_iInter_of_finite fun α =>
    isOpen_lt continuous_const ((continuous_apply α).comp (continuous_fst.comp he))

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "πG" => LeftCosetSpace.mk (rationalSubgroup F G)

/-- **Null sets of the weighted automorphic measure are Haar null.** If every point of `G(𝔸)`
has a rational translate whose height lies in the Borel region `S₀`, a measurable set of
`G(F) \ G(𝔸)` that is null for the automorphic measure of `S₀` has Haar-null preimage in
`G(𝔸)`. -/
theorem haar_preimage_eq_zero (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S₀ : Set (RealCharacterDual F P)) (hS₀ : @MeasurableSet _ (borel _) S₀)
    (hcover : ∀ y : A, ∃ q : RationalGroupPoints F G, hK.height (rational F G q * y) ∈ S₀)
    {E : Set (RationalQuotient F G)} (hE : MeasurableSet E)
    (h0 : automorphicMeasure F p hK ell (domainHeight F p hK ⁻¹' S₀) E = 0) :
    (Measure.haar : Measure A) (πG ⁻¹' E) = 0 := by
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  have : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  set Γ := parabolicPrincipalSubgroup F p
  set D := LeftCosetSpace.fundamentalDomain Γ (isDiscrete_parabolicPrincipalSubgroup F p)
  have hD : MeasurableSet D := LeftCosetSpace.measurableSet_fundamentalDomain _ _
  have hmkE : MeasurableSet (toAutomorphic F p ⁻¹' E) :=
    (continuous_toAutomorphic F p).measurable hE
  have hφ : Measurable ((toAutomorphic F p ⁻¹' E).indicator (1 : DomainQuotient F p → ℝ≥0∞)) :=
    measurable_const.indicator hmkE
  -- the weighted integral over the fundamental domain vanishes
  have hint : ∫⁻ g in D, (toAutomorphic F p ⁻¹' E).indicator 1
      (LeftCosetSpace.mk Γ g) * chamberDensity F p hK ell S₀ g ∂Measure.haar = 0 := by
    rw [← lintegral_domainMeasure_eq_chamberDensity F p hK ell hell S₀ hS₀ hφ,
      lintegral_indicator_one hmkE]
    rwa [automorphicMeasure, Measure.map_apply (continuous_toAutomorphic F p).measurable hE] at h0
  have hmeas : Measurable fun g : A => (toAutomorphic F p ⁻¹' E).indicator 1
      (LeftCosetSpace.mk Γ g) * chamberDensity F p hK ell S₀ g := by
    refine (hφ.comp (LeftCosetSpace.measurable_mk _)).mul ?_
    exact (ENNReal.continuous_ofReal.comp ((continuous_const.mul
      (hell.comp hK.continuous_height)).rexp)).measurable.indicator
      (hK.continuous_height.measurable hS₀)
  have hae := (lintegral_eq_zero_iff hmeas).mp hint
  -- the part of the fundamental domain over `E` with height in `S₀` is null
  set Z := (πG ⁻¹' E ∩ hK.height ⁻¹' S₀) ∩ D with hZ
  have hsub : πG ⁻¹' E ∩ hK.height ⁻¹' S₀ ⊆ {g | ¬ ((toAutomorphic F p ⁻¹' E).indicator 1
      (LeftCosetSpace.mk Γ g) * chamberDensity F p hK ell S₀ g = (0 : A → ℝ≥0∞) g)} := by
    rintro g ⟨hgE, hgS⟩
    simp only [mem_ofPred_eq, Pi.zero_apply]
    rw [indicator_of_mem (show LeftCosetSpace.mk Γ g ∈ toAutomorphic F p ⁻¹' E from hgE),
      chamberDensity, indicator_of_mem (show g ∈ hK.height ⁻¹' S₀ from hgS)]
    simp [Real.exp_pos]
  have hZ0 : (Measure.haar : Measure A) Z = 0 := by
    rw [hZ, ← Measure.restrict_apply' hD]
    exact measure_mono_null hsub (ae_iff.mp hae)
  -- every point over `E` has a rational translate in `Z`
  have hcov : πG ⁻¹' E ⊆ ⋃ c : rationalSubgroup F G, (fun y : A => c.val * y) ⁻¹' Z := by
    intro y hy
    obtain ⟨q, hq⟩ := hcover y
    obtain ⟨l, hl, -⟩ := LeftCosetSpace.fundamentalDomain_unique Γ
      (isDiscrete_parabolicPrincipalSubgroup F p) (rational F G q * y)
    have hlr : (l : A) ∈ rationalSubgroup F G := parabolicPrincipalSubgroup_le F p l.property
    refine mem_iUnion.mpr ⟨⟨(l : A) * rational F G q, (rationalSubgroup F G).mul_mem hlr
      ⟨q, rfl⟩⟩, ?_⟩
    simp only [mem_preimage]
    rw [mul_assoc]
    refine ⟨⟨?_, ?_⟩, hl⟩
    · change LeftCosetSpace.mk (rationalSubgroup F G) ((l : A) * (rational F G q * y)) ∈ E
      rw [show (l : A) * (rational F G q * y) = ((l : A) * rational F G q) * y by rw [mul_assoc],
        LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G)
          ⟨(l : A) * rational F G q, (rationalSubgroup F G).mul_mem hlr ⟨q, rfl⟩⟩ y]
      exact hy
    · obtain ⟨_, ⟨q', rfl⟩, hq'⟩ := l.property
      change hK.height ((l : A) * (rational F G q * y)) ∈ S₀
      rw [← hq']
      change hK.height (map F P G p (rational F P q') * (rational F G q * y)) ∈ S₀
      rw [hK.height_rational_mul]
      exact hq
  refine measure_mono_null hcov (measure_iUnion_null fun c => ?_)
  rw [measure_preimage_mul]
  exact hZ0

/-- **Smoothing operators on the weighted Siegel space.** Let `e` be linear coordinates on the real
dual of `P` with root part indexed by `Δ`, and let every `x ∈ G(𝔸)` have a rational translate
`q x` with finite component in a compact `Ω`, root coordinates `(e(H(q x)))_α ≥ θ_α` and
`ht(q x) ≤ M ht(x)^t`. For every finite family of smooth compactly supported kernels `h_k` there
is `δ ≥ 0` with the following property. For every `τ` with `τ_α + δ < θ_α` and all rates `ra`,
`rb` whose log weight `ell = localFinitenessLogWeight ra rb ∘ e` satisfies
`exp(ell(H g)) ≤ W ht(g)^r'`, there is `R₀ ≥ 0` such that for every `R ≥ R₀` and every level `L`
under which the kernels are left invariant, the weighted Hilbert space of the Siegel region
`siegelHeightRegion e τ` carries continuous linear maps `K_k` into `𝔉^R_L` with `K_k b = δ(h_k) f`
for every measurable `f` on `G(F) \ G(𝔸)` representing `b`. -/
theorem exists_smoothingOperators {n d : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (hn : 0 < n) (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    {Δ : Type*} [Fintype Δ] {r : ℕ} (e : RealCharacterDual F P ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ)))
    (θ : Δ → ℝ) (Ω : Set (FiniteAdelicGroupPoints F G)) (hΩ : IsCompact Ω) (M t : ℝ)
    (hM : 0 < M) (ht : 0 ≤ t)
    (hY : ∀ x : A, ∃ q : RationalGroupPoints F G,
      AdelicGroupPoints.finite F G (rational F G q * x) ∈ Ω ∧
      (∀ α, θ α ≤ (e (hK.height (rational F G q * x))).1 α) ∧
      adelicHeight F G rho (rational F G q * x) ≤ M * adelicHeight F G rho x ^ t)
    {I : Type*} [Finite I] (h : I → A → ℂ) (hh : ∀ k, IsAdelicTestFunction F G (h k)) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ τ : Δ → ℝ, (∀ α, τ α + δ < θ α) →
      ∀ (ra : Δ → ℝ) (rb : Fin r → ℝ) (W r' : ℝ), 0 < W → 0 ≤ r' →
      (∀ g : A, Real.exp (localFinitenessLogWeight ra rb (e (hK.height g))) ≤
        W * adelicHeight F G rho g ^ r') →
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ (L : Subgroup (FiniteAdelicGroupPoints F G)),
        (∀ k, ∀ l ∈ L, ∀ x, h k (ofFinite F G l * x) = h k x) →
        ∃ Ksm : I → (HilbertSpace F p hK (localFinitenessLogWeight ra rb ∘ e)
            (domainHeight F p hK ⁻¹' siegelHeightRegion e τ) →L[ℂ]
              UniformGrowthFrechetSpace F G rho hsmooth hcalc hn hrho R L),
          ∀ k (b : HilbertSpace F p hK (localFinitenessLogWeight ra rb ∘ e)
              (domainHeight F p hK ⁻¹' siegelHeightRegion e τ)) (f : RationalQuotient F G → ℂ),
            Measurable f →
            f =ᵐ[automorphicMeasure F p hK (localFinitenessLogWeight ra rb ∘ e)
              (domainHeight F p hK ⁻¹' siegelHeightRegion e τ)] ⇑b →
            ∀ x, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hn hrho R L (Ksm k b) x =
              rightConvolution F G (h k) (f ∘ πG) x := by
  let Y : Set A := {y | AdelicGroupPoints.finite F G y ∈ Ω ∧ ∀ α, θ α ≤ (e (hK.height y)).1 α}
  have hYcov : ∀ x : A, ∃ q : rationalSubgroup F G, q.val * x ∈ Y ∧
      adelicHeight F G rho (q.val * x) ≤ M * adelicHeight F G rho x ^ t := by
    intro x
    obtain ⟨q, h1, h2, h3⟩ := hY x
    exact ⟨⟨rational F G q, q, rfl⟩, ⟨h1, h2⟩, h3⟩
  let C : Set A := ⋃ k, tsupport (h k)
  have hC : IsCompact C := isCompact_iUnion fun k => (hh k).2.1
  let φ (α : Δ) : RealCharacterDual F P →ₗ[ℝ] ℝ :=
    (LinearMap.proj α).comp ((LinearMap.fst ℝ (Δ → ℝ) (Fin r → ℝ)).comp e.toLinearEquiv.toLinearMap)
  have hφc : ∀ α ∈ (Finset.univ : Finset Δ), Continuous (φ α) := fun α _ =>
    ((continuous_apply α).comp continuous_fst).comp e.continuous
  obtain ⟨δ, hδ, hshift⟩ := hK.iwasawaHeightCoordinateRightShift Finset.univ φ hφc C hC
  refine ⟨δ, hδ, fun τ hτ ra rb W r' hW hr' hweight => ?_⟩
  set ell := localFinitenessLogWeight ra rb ∘ e with hell_def
  have hell : Continuous ell := (continuous_localFinitenessLogWeight ra rb).comp e.continuous
  obtain ⟨R₀, hR₀, hsm⟩ := adelicWeightedSmoothingOperator hK rho hsmooth hcalc hn hrho ell hell
    W r' hW hr' hweight Y M t hM ht hYcov
  refine ⟨R₀, hR₀, fun R hR L hL => ?_⟩
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  have : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  set S := siegelHeightRegion (⇑e) τ with hSdef
  have hSo : IsOpen S := isOpen_siegelHeightRegion e.continuous τ
  have hSm : MeasurableSet S := hSo.measurableSet
  have hYS : MapsTo hK.height Y S := fun y hy α => by linarith [hy.2 α, hτ α]
  have hYa : ∀ k, ∀ x ∈ Y, ∀ a ∈ tsupport (h k), hK.height (x * a) ∈ S := by
    intro k x hx a ha α
    have hb := hshift x a (mem_iUnion.mpr ⟨k, ha⟩) α (Finset.mem_univ α)
    have e1 : φ α (hK.height (x * a)) = (e (hK.height (x * a))).1 α := rfl
    have e2 : φ α (hK.height x) = (e (hK.height x)).1 α := rfl
    rw [e1, e2] at hb
    have h1 := (abs_le.mp hb).1
    change τ α < (e (hK.height (x * a))).1 α
    linarith [hx.2 α, hτ α]
  obtain ⟨s, rep, hs, hrep, hrepm, hrepinv, hbound⟩ := weightedHilbertRealization hK ell hell S
  have hnorm : ∀ v, chamberSquareIntegral hK ell S (rep v) < ∞ ∧
      Real.sqrt (chamberSquareIntegral hK ell S (rep v)).toReal ≤ 1 * ‖v‖ := by
    intro v
    have := hbound S hSm 1 zero_le_one (by simp) v
    simpa using this
  choose Ksm hKsm using fun k => hsm R hR Ω hΩ (fun y hy => hy.1) S hSo hYS (h k) (hh k)
    (hYa k) L (hL k) _ rep hrepm hrepinv 1 zero_le_one hnorm
  refine ⟨Ksm, fun k b f hf hfb x => ?_⟩
  rw [hKsm k b x]
  have hcover : ∀ y : A, ∃ q : RationalGroupPoints F G, hK.height (rational F G q * y) ∈ S :=
    fun y => by
      obtain ⟨q, h1, h2, -⟩ := hY y
      exact ⟨q, hYS ⟨h1, h2⟩⟩
  set E : Set (RationalQuotient F G) := {z | s b z ≠ f z} with hEdef
  have hE : MeasurableSet E := (measurableSet_eq_fun (hs b).1 hf).compl
  have hE0 : automorphicMeasure F p hK ell (domainHeight F p hK ⁻¹' S) E = 0 :=
    ae_iff.mp ((hs b).2.trans hfb.symm)
  have hnull := haar_preimage_eq_zero hK ell hell S hSm hcover hE hE0
  have hg : ∀ᵐ g ∂(Measure.haar : Measure A), x * g ∉ πG ⁻¹' E := by
    rw [ae_iff]
    simp only [not_not]
    change (Measure.haar : Measure A) ((fun g => x * g) ⁻¹' (πG ⁻¹' E)) = 0
    rw [measure_preimage_mul]
    exact hnull
  unfold rightConvolution
  refine integral_congr_ae ?_
  filter_upwards [hg] with g hg
  simp only [mem_preimage, hEdef, mem_ofPred_eq, ne_eq, not_not] at hg
  rw [hrep b]
  simp only [Function.comp_apply, hg]

end Langlands.Global.WeightedSiegel
