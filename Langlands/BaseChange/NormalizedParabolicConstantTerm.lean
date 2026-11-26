import Langlands.AllField.Group.GL.BlockModulus
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.Group.GL.IntegralSubgroup
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct

/-!
# Normalized ordinary and twisted parabolic constant terms

For a nonarchimedean local field `E`, a standard block shape `B` of `n`, and a
continuous automorphism `θ` of `G = GL_n(E)`, this module constructs the complex-linear
map from Schwartz–Bruhat functions on `G` to Schwartz–Bruhat functions on the actual
block Levi `B.Levi E`,
`φ ↦ (m ↦ δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u θ(k)) dk du)`,
after Henniart–Lemaire (2011), II.4.5, and Laumon (1996), (4.4.7). Here
`K = GL_n(𝒪_E)` carries its Haar probability measure, `U` is the unipotent radical of
the standard block parabolic with the Haar measure giving `U ∩ K` volume one, and
`δ_P^{1/2}` is `LocalFieldData.leviHalfModulus`. The ordinary map is the case
`θ = 1` and the twisted map the case `θ = entrywiseAut σ n`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Topology Set

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis Langlands.GeneralLinear

namespace ParabolicConstantTerm

universe uX uY uG uE

/-! ### Operations on Schwartz–Bruhat functions -/

section Operations

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two Schwartz–Bruhat functions with the same values are equal. -/
theorem schwartzBruhat_ext {f g : SchwartzBruhat X} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

/-- The restriction of a Schwartz–Bruhat function along a closed embedding. -/
def restrict (f : SchwartzBruhat X) {i : Y → X} (hi : IsClosedEmbedding i) :
    SchwartzBruhat Y :=
  ⟨fun y => f (i y), f.locallyConstant.comp_continuous hi.continuous,
    f.hasCompactSupport.comp_isClosedEmbedding hi⟩

@[simp] theorem restrict_apply (f : SchwartzBruhat X) {i : Y → X} (hi : IsClosedEmbedding i)
    (y : Y) : restrict f hi y = f (i y) := rfl

/-- Multiplication by a fixed locally constant function, as a linear map. -/
def mulLocallyConstant {c : X → ℂ} (hc : IsLocallyConstant c) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨fun x => c x * f x, hc.comp₂ f.locallyConstant (· * ·),
    f.hasCompactSupport.mul_left⟩
  map_add' f g := schwartzBruhat_ext fun x => by
    change c x * (f x + g x) = c x * f x + c x * g x
    ring
  map_smul' a f := schwartzBruhat_ext fun x => by
    change c x * (a * f x) = a * (c x * f x)
    ring

@[simp] theorem mulLocallyConstant_apply {c : X → ℂ} (hc : IsLocallyConstant c)
    (f : SchwartzBruhat X) (x : X) : mulLocallyConstant hc f x = c x * f x := rfl

/-- The constant function one on a compact space. -/
def constOne [CompactSpace X] : SchwartzBruhat X :=
  ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩

@[simp] theorem constOne_apply [CompactSpace X] (x : X) : (constOne : SchwartzBruhat X) x = 1 :=
  rfl

/-- A homomorphism to `ℂˣ` with open kernel is locally constant. -/
theorem isLocallyConstant_of_isOpen_ker {M : Type uX} [Group M] [TopologicalSpace M]
    [ContinuousMul M] (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) :
    IsLocallyConstant fun m => (χ m : ℂ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro m
  refine ⟨(fun t : M => m⁻¹ * t) ⁻¹' (χ.ker : Set M),
    hχ.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro t ht
    have ht' : χ (m⁻¹ * t) = 1 := ht
    rw [map_mul, map_inv, inv_mul_eq_one] at ht'
    rw [ht']

end Operations

/-! ### The twisted compact average -/

section Average

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  (K : Subgroup G) [CompactSpace K] (θ : G → G) (hθ : Continuous θ)

/-- The function `(g, k) ↦ φ (k⁻¹ * g * θ k)` on `G × K`. It is Schwartz–Bruhat because
`(g, k) ↦ (k⁻¹ * g * θ k, k)` has the continuous left inverse
`(g, k) ↦ (k * g * (θ k)⁻¹, k)`. -/
def twistedConjugationKernel (φ : SchwartzBruhat G) : SchwartzBruhat (G × K) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor φ (constOne : SchwartzBruhat K))
    (fun y : G × K => ((y.2 : G)⁻¹ * y.1 * θ y.2, y.2))
    (fun x : G × K => ((x.2 : G) * x.1 * (θ x.2)⁻¹, x.2))
    ((((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul
      (hθ.comp (continuous_subtype_val.comp continuous_snd))).prodMk continuous_snd)
    ((((continuous_subtype_val.comp continuous_snd).mul continuous_fst).mul
      (hθ.comp (continuous_subtype_val.comp continuous_snd)).inv).prodMk continuous_snd)
    (fun y => by
      ext
      · simp [mul_assoc]
      · rfl)

@[simp] theorem twistedConjugationKernel_apply (φ : SchwartzBruhat G) (g : G) (k : K) :
    twistedConjugationKernel K θ hθ φ (g, k) = φ ((k : G)⁻¹ * g * θ k) := by
  simp [twistedConjugationKernel]

variable [MeasurableSpace K] [OpensMeasurableSpace K] (μK : Measure K)
  [IsFiniteMeasureOnCompacts μK]

include hθ in
/-- Integrability on the compact fibre. -/
theorem integrable_twistedConjugation (φ : SchwartzBruhat G) (g : G) :
    Integrable (fun k : K => φ ((k : G)⁻¹ * g * θ k)) μK := by
  have h := (SchwartzBruhat.sliceSnd (twistedConjugationKernel K θ hθ φ) g).integrable μK
  convert h using 1
  funext k
  simp

/-- The twisted compact average `g ↦ ∫ k, φ (k⁻¹ * g * θ k) dk`. -/
def twistedCompactAverage : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun φ := SchwartzBruhat.partialIntegral (twistedConjugationKernel K θ hθ φ) μK
  map_add' φ ψ := schwartzBruhat_ext fun g => by
    change ∫ k, twistedConjugationKernel K θ hθ (φ + ψ) (g, k) ∂μK =
      ∫ k, twistedConjugationKernel K θ hθ φ (g, k) ∂μK +
        ∫ k, twistedConjugationKernel K θ hθ ψ (g, k) ∂μK
    simp only [twistedConjugationKernel_apply]
    rw [← integral_add (integrable_twistedConjugation K θ hθ μK φ g)
      (integrable_twistedConjugation K θ hθ μK ψ g)]
    rfl
  map_smul' a φ := schwartzBruhat_ext fun g => by
    change ∫ k, twistedConjugationKernel K θ hθ (a • φ) (g, k) ∂μK =
      a * ∫ k, twistedConjugationKernel K θ hθ φ (g, k) ∂μK
    simp only [twistedConjugationKernel_apply]
    rw [← integral_const_mul]
    rfl

@[simp] theorem twistedCompactAverage_apply (φ : SchwartzBruhat G) (g : G) :
    twistedCompactAverage K θ hθ μK φ g = ∫ k, φ ((k : G)⁻¹ * g * θ k) ∂μK := by
  change ∫ k, twistedConjugationKernel K θ hθ φ (g, k) ∂μK = _
  simp only [twistedConjugationKernel_apply]

end Average

/-! ### Integration over the unipotent radical -/

section Parabolic

variable {E : Type uE} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  {n : ℕ} (B : BlockShape n)

omit [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] in
/-- Removing the Levi component of a parabolic element leaves an element of the radical. -/
theorem leviInParabolic_inv_mul_mem (p : B.parabolic E) :
    (B.leviInParabolic E (B.leviProjection E p))⁻¹ * p ∈ B.unipotentRadical E := by
  change B.leviProjection E ((B.leviInParabolic E (B.leviProjection E p))⁻¹ * p) = 1
  rw [map_mul, map_inv, BlockShape.leviProjection_section, inv_mul_cancel]

omit [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] in
/-- The Levi projection of `m * u` is `m`. -/
theorem leviProjection_leviInParabolic_mul (m : B.Levi E) (u : B.unipotentRadical E) :
    B.leviProjection E (B.leviInParabolic E m * u) = m := by
  have hu : B.leviProjection E (u : B.parabolic E) = 1 := u.property
  rw [map_mul, BlockShape.leviProjection_section, hu, mul_one]

/-- The factorization `(m, u) ↦ m * u` of the standard parabolic `P` as `M × U`,
with inverse `p ↦ (m, m⁻¹ * p)` for the Levi projection `m` of `p`. -/
def leviRadicalEquiv : B.Levi E × B.unipotentRadical E ≃ B.parabolic E where
  toFun x := B.leviInParabolic E x.1 * x.2
  invFun p := (B.leviProjection E p, ⟨_, leviInParabolic_inv_mul_mem B p⟩)
  left_inv x := by
    obtain ⟨m, u⟩ := x
    refine Prod.ext (leviProjection_leviInParabolic_mul B m u) (Subtype.ext ?_)
    change (B.leviInParabolic E (B.leviProjection E (B.leviInParabolic E m * u)))⁻¹ *
      (B.leviInParabolic E m * u) = u
    rw [leviProjection_leviInParabolic_mul B m u, inv_mul_cancel_left]
  right_inv p := mul_inv_cancel_left _ _

/-- The homeomorphism `(m, u) ↦ m * u` from `M × U` onto the standard parabolic `P`. -/
def leviRadicalHomeomorph : B.Levi E × B.unipotentRadical E ≃ₜ B.parabolic E where
  toEquiv := leviRadicalEquiv B
  continuous_toFun :=
    ((B.leviInParabolicContinuous E).continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (B.leviProjectionContinuous E).continuous.prodMk
      ((((B.leviInParabolicContinuous E).continuous.comp
        (B.leviProjectionContinuous E).continuous).inv.mul continuous_id).subtype_mk _)

omit [T2Space E] in
@[simp] theorem leviRadicalHomeomorph_apply (x : B.Levi E × B.unipotentRadical E) :
    leviRadicalHomeomorph B x = B.leviInParabolic E x.1 * x.2 := rfl

/-- The map `(m, u) ↦ m * u` into `GL_n(E)` is a closed embedding. -/
theorem isClosedEmbedding_leviRadical :
    IsClosedEmbedding (fun x : B.Levi E × B.unipotentRadical E =>
      ((leviRadicalHomeomorph B x : B.parabolic E) : GeneralLinear n E)) :=
  (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.comp
    (leviRadicalHomeomorph B).isClosedEmbedding

/-- The inclusion of the unipotent radical into `GL_n(E)` is a closed embedding. -/
theorem isClosedEmbedding_radicalVal :
    IsClosedEmbedding (fun u : B.unipotentRadical E => ((u : B.parabolic E) : GeneralLinear n E)) :=
  (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.comp
    (B.isClosed_unipotentRadical E).isClosedEmbedding_subtypeVal

variable [MeasurableSpace (B.unipotentRadical E)] [OpensMeasurableSpace (B.unipotentRadical E)]
  (μU : Measure (B.unipotentRadical E)) [IsFiniteMeasureOnCompacts μU]

/-- Integrability on the fibre over a Levi element. -/
theorem integrable_radical (f : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    Integrable (fun u : B.unipotentRadical E =>
      f (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E))) μU := by
  exact (SchwartzBruhat.sliceSnd (restrict f (isClosedEmbedding_leviRadical B)) m).integrable μU

/-- The radical integral `f ↦ (m ↦ ∫ u, f (m * u) du)`, valued in Schwartz–Bruhat
functions on the actual Levi. -/
def radicalIntegral : SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E) where
  toFun f := SchwartzBruhat.partialIntegral (restrict f (isClosedEmbedding_leviRadical B)) μU
  map_add' f g := schwartzBruhat_ext fun m => by
    change ∫ u, (f + g) (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU =
      ∫ u, f (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU +
        ∫ u, g (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU
    rw [← integral_add (integrable_radical B μU f m) (integrable_radical B μU g m)]
    rfl
  map_smul' a f := schwartzBruhat_ext fun m => by
    change ∫ u, (a • f) (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU =
      a * ∫ u, f (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU
    rw [← integral_const_mul]
    rfl

@[simp] theorem radicalIntegral_apply (f : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    radicalIntegral B μU f m =
      ∫ u, f (B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E)) ∂μU := rfl

end Parabolic

end ParabolicConstantTerm

open ParabolicConstantTerm

universe uE uF

/-! ### The constant term over a nonarchimedean local field -/

section LocalField

variable (E : Type uE) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

/-- The positive half modulus `δ_P^{1/2}` of the standard block parabolic is locally
constant on the actual Levi, since its kernel is open. -/
theorem isLocallyConstant_leviHalfModulus :
    IsLocallyConstant fun m : B.Levi E =>
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) :=
  isLocallyConstant_of_isOpen_ker _ ((LocalFieldData.ofInstances E).isOpen_ker_leviHalfModulus B)

section Generic

variable (K : Subgroup (GeneralLinear n E)) (hK : IsCompact (K : Set (GeneralLinear n E)))
  [MeasurableSpace K] [OpensMeasurableSpace K] (μK : Measure K) [IsFiniteMeasureOnCompacts μK]
  [MeasurableSpace (B.unipotentRadical E)] [OpensMeasurableSpace (B.unipotentRadical E)]
  (μU : Measure (B.unipotentRadical E)) [IsFiniteMeasureOnCompacts μU]
  (θ : GeneralLinear n E ≃* GeneralLinear n E) (hθ : Continuous θ)

/-- The normalized `θ`-twisted constant term along the standard block parabolic, for an
arbitrary compact subgroup `K` of `GL_n(E)` and arbitrary measures `μK` on `K` and `μU` on
the unipotent radical, finite on compact sets:
`φ ↦ (m ↦ δ_P(m)^{1/2} ∫ u, ∫ k, φ (k⁻¹ * m * u * θ k) dμK dμU)`. -/
def parabolicConstantTermOfCompact :
    SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E) :=
  haveI := LocalFieldTopology.t2Space E
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  mulLocallyConstant (isLocallyConstant_leviHalfModulus E B) ∘ₗ radicalIntegral B μU ∘ₗ
    twistedCompactAverage K θ hθ μK

/-- **Evaluation.** The value at `m` is
`δ_P(m)^{1/2} ∫ u, ∫ k, φ (k⁻¹ * m * u * θ k) dμK dμU`, with `m` included by the actual
block diagonal embedding and `u` in the actual unipotent radical. -/
theorem parabolicConstantTermOfCompact_apply (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    parabolicConstantTermOfCompact E B K hK μK μU θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k) ∂μK ∂μU := by
  have := LocalFieldTopology.t2Space E
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  simp only [parabolicConstantTermOfCompact, LinearMap.coe_comp, Function.comp_apply,
    mulLocallyConstant_apply, radicalIntegral_apply, twistedCompactAverage_apply, mul_assoc]

include hK hθ in
/-- Integrability on the compact fibre: for every `g`, `k ↦ φ (k⁻¹ * g * θ k)` is
integrable. -/
theorem integrable_compactFibre (φ : SchwartzBruhat (GeneralLinear n E))
    (g : GeneralLinear n E) :
    Integrable (fun k : K => φ ((k : GeneralLinear n E)⁻¹ * g * θ k)) μK := by
  have := LocalFieldTopology.t2Space E
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact integrable_twistedConjugation K θ hθ μK φ g

include hK hθ in
/-- Integrability on the radical fibre: for every Levi element `m`, the inner compact
integral is integrable in `u`. -/
theorem integrable_radicalFibre (φ : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    Integrable (fun u : B.unipotentRadical E => ∫ k, φ ((k : GeneralLinear n E)⁻¹ *
      B.leviEmbedding E m * ((u : B.parabolic E) : GeneralLinear n E) * θ k) ∂μK) μU := by
  have := LocalFieldTopology.t2Space E
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h := integrable_radical B μU (twistedCompactAverage K θ hθ μK φ) m
  simp only [twistedCompactAverage_apply] at h
  simpa only [mul_assoc] using h

include hK hθ in
/-- Integrability on the product fibre `U × K`, for the product measure. -/
theorem integrable_productFibre (φ : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    Integrable (fun p : B.unipotentRadical E × K => φ ((p.2 : GeneralLinear n E)⁻¹ *
      B.leviEmbedding E m * ((p.1 : B.parabolic E) : GeneralLinear n E) * θ p.2))
      (μU.prod μK) := by
  have := LocalFieldTopology.t2Space E
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have := LocalFieldTopology.generalLinear_secondCountableTopology E n
  have : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set (GeneralLinear n E))
  have hj : IsClosedEmbedding (fun p : B.unipotentRadical E × K =>
      (B.leviEmbedding E m * ((p.1 : B.parabolic E) : GeneralLinear n E), p.2)) :=
    ((Homeomorph.mulLeft (B.leviEmbedding E m)).isClosedEmbedding.comp
      (isClosedEmbedding_radicalVal B)).prodMap IsClosedEmbedding.id
  have h := (restrict (twistedConjugationKernel K θ hθ φ) hj).integrable (μU.prod μK)
  convert h using 1
  funext p
  simp [mul_assoc]

/-- **Evaluation in the other order.** The compact integral may be taken outside. -/
theorem parabolicConstantTermOfCompact_apply_swap [SFinite μU]
    (φ : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    parabolicConstantTermOfCompact E B K hK μK μU θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ k, ∫ u, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k) ∂μU ∂μK := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [parabolicConstantTermOfCompact_apply,
    integral_integral_swap (integrable_productFibre E B K hK μK μU θ hθ φ m)]

/-- **Evaluation as a product integral** over `U × K`. -/
theorem parabolicConstantTermOfCompact_apply_prod [SFinite μU]
    (φ : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    parabolicConstantTermOfCompact E B K hK μK μU θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ p : B.unipotentRadical E × K, φ ((p.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((p.1 : B.parabolic E) : GeneralLinear n E) * θ p.2) ∂(μU.prod μK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [parabolicConstantTermOfCompact_apply,
    integral_prod _ (integrable_productFibre E B K hK μK μU θ hθ φ m)]

end Generic

/-! ### The standard maximal compact subgroup and the normalized Haar measures -/

section Standard

variable (n)

/-- The standard maximal compact subgroup `K = GL_n(𝒪_E)`: invertible matrices whose
entries, and the entries of whose inverse, lie in the valuation ring. -/
abbrev standardMaximalCompact : Subgroup (GeneralLinear n E) :=
  Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer

theorem isOpen_standardMaximalCompact :
    IsOpen (standardMaximalCompact E n : Set (GeneralLinear n E)) :=
  Langlands.GeneralLinearGroup.isOpen_integralSubgroup (Fin n) _
    (GeneralLocalField.isOpen_integer E)

theorem isCompact_standardMaximalCompact :
    IsCompact (standardMaximalCompact E n : Set (GeneralLinear n E)) := by
  have := LocalFieldTopology.t2Space E
  exact Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin n) _
    (GeneralLocalField.isCompact_integer E)

instance compactSpace_standardMaximalCompact : CompactSpace (standardMaximalCompact E n) :=
  isCompact_iff_compactSpace.mp (isCompact_standardMaximalCompact E n)

section CompactHaar

variable [MeasurableSpace (standardMaximalCompact E n)] [BorelSpace (standardMaximalCompact E n)]

/-- The Haar probability measure on `K = GL_n(𝒪_E)`. -/
def standardCompactHaar : Measure (standardMaximalCompact E n) :=
  Measure.haarMeasure ⊤

instance isHaarMeasure_standardCompactHaar : (standardCompactHaar E n).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance isProbabilityMeasure_standardCompactHaar :
    IsProbabilityMeasure (standardCompactHaar E n) :=
  ⟨by
    have h := Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (standardMaximalCompact E n)))
    rw [TopologicalSpace.PositiveCompacts.coe_top] at h
    exact h⟩

/-- `K` has volume one. -/
theorem standardCompactHaar_univ : standardCompactHaar E n univ = 1 :=
  measure_univ

/-- Every left-invariant probability measure on `K` is `standardCompactHaar`. -/
theorem eq_standardCompactHaar (μ : Measure (standardMaximalCompact E n))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ = standardCompactHaar E n := by
  have := LocalFieldTopology.generalLinear_secondCountableTopology E n
  have : SecondCountableTopology (standardMaximalCompact E n) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (standardMaximalCompact E n : Set (GeneralLinear n E))
  rw [Measure.haarMeasure_unique μ ⊤, TopologicalSpace.PositiveCompacts.coe_top, measure_univ,
    one_smul]
  rfl

end CompactHaar

variable {n}

/-- `U ∩ K = U(𝒪_E)`, as a compact subset of the unipotent radical with nonempty interior. -/
def radicalCompact : TopologicalSpace.PositiveCompacts (B.unipotentRadical E) where
  carrier := {u | ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n}
  isCompact' := by
    have := LocalFieldTopology.t2Space E
    exact (isClosedEmbedding_radicalVal B).isCompact_preimage
      (isCompact_standardMaximalCompact E n)
  interior_nonempty' := by
    have hopen : IsOpen {u : B.unipotentRadical E |
        ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} :=
      (isOpen_standardMaximalCompact E n).preimage
        (continuous_subtype_val.comp continuous_subtype_val)
    rw [hopen.interior_eq]
    exact ⟨1, (standardMaximalCompact E n).one_mem⟩

@[simp] theorem coe_radicalCompact :
    (radicalCompact E B : Set (B.unipotentRadical E)) =
      {u : B.unipotentRadical E |
        ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} := rfl

/-- The unipotent radical is second countable. -/
theorem secondCountableTopology_unipotentRadical :
    SecondCountableTopology (B.unipotentRadical E) := by
  have := LocalFieldTopology.generalLinear_secondCountableTopology E n
  have : SecondCountableTopology (B.parabolic E) :=
    TopologicalSpace.Subtype.secondCountableTopology (B.parabolic E : Set (GeneralLinear n E))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (B.unipotentRadical E : Set (B.parabolic E))

section RadicalHaar

variable [MeasurableSpace (B.unipotentRadical E)] [BorelSpace (B.unipotentRadical E)]

/-- The Haar measure on the unipotent radical `U` giving `U ∩ K` volume one. -/
def standardRadicalHaar : Measure (B.unipotentRadical E) :=
  Measure.haarMeasure (radicalCompact E B)

instance isHaarMeasure_standardRadicalHaar : (standardRadicalHaar E B).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-- `U ∩ K` has volume one. -/
theorem standardRadicalHaar_radicalCompact :
    standardRadicalHaar E B
      {u | ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} = 1 :=
  Measure.haarMeasure_self

instance sigmaFinite_standardRadicalHaar : SigmaFinite (standardRadicalHaar E B) := by
  have := secondCountableTopology_unipotentRadical E B
  exact Measure.sigmaFinite_haarMeasure

/-- Every Haar measure on `U` giving `U ∩ K` volume one is `standardRadicalHaar`. -/
theorem eq_standardRadicalHaar (μ : Measure (B.unipotentRadical E)) [μ.IsHaarMeasure]
    (hμ : μ {u | ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} = 1) :
    μ = standardRadicalHaar E B := by
  have := secondCountableTopology_unipotentRadical E B
  have := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  have := LocalFieldTopology.t2Space E
  have := B.unipotentRadicalLocallyCompactSpace E
  rw [Measure.haarMeasure_unique μ (radicalCompact E B), coe_radicalCompact, hμ, one_smul]
  rfl

end RadicalHaar

/-! ### The normalized constant terms -/

variable [MeasurableSpace (standardMaximalCompact E n)] [BorelSpace (standardMaximalCompact E n)]
  [MeasurableSpace (B.unipotentRadical E)] [BorelSpace (B.unipotentRadical E)]
  (θ : GeneralLinear n E ≃* GeneralLinear n E) (hθ : Continuous θ)

/-- **The normalized `θ`-twisted parabolic constant term** (Henniart–Lemaire, II.4.5):
`φ ↦ (m ↦ δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u θ(k)) dk du)`, with the Haar probability on
`K = GL_n(𝒪_E)` and the Haar measure on `U` giving `U ∩ K` volume one. -/
def normalizedAutParabolicConstantTerm :
    SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E) :=
  parabolicConstantTermOfCompact E B (standardMaximalCompact E n)
    (isCompact_standardMaximalCompact E n) (standardCompactHaar E n) (standardRadicalHaar E B)
    θ hθ

theorem normalizedAutParabolicConstantTerm_eq :
    normalizedAutParabolicConstantTerm E B θ hθ =
      parabolicConstantTermOfCompact E B (standardMaximalCompact E n)
        (isCompact_standardMaximalCompact E n) (standardCompactHaar E n)
        (standardRadicalHaar E B) θ hθ := rfl

/-- **Evaluation** of the normalized `θ`-twisted constant term. -/
theorem normalizedAutParabolicConstantTerm_apply (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    normalizedAutParabolicConstantTerm E B θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k)
          ∂(standardCompactHaar E n) ∂(standardRadicalHaar E B) :=
  parabolicConstantTermOfCompact_apply E B _ _ _ _ θ hθ φ m

/-- Evaluation of the normalized `θ`-twisted constant term, compact integral outside. -/
theorem normalizedAutParabolicConstantTerm_apply_swap (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    normalizedAutParabolicConstantTerm E B θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ k, ∫ u, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k)
          ∂(standardRadicalHaar E B) ∂(standardCompactHaar E n) :=
  parabolicConstantTermOfCompact_apply_swap E B _ _ _ _ θ hθ φ m

/-- Evaluation of the normalized `θ`-twisted constant term as a product integral. -/
theorem normalizedAutParabolicConstantTerm_apply_prod (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    normalizedAutParabolicConstantTerm E B θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ p : B.unipotentRadical E × standardMaximalCompact E n,
          φ ((p.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
            ((p.1 : B.parabolic E) : GeneralLinear n E) * θ p.2)
          ∂((standardRadicalHaar E B).prod (standardCompactHaar E n)) :=
  parabolicConstantTermOfCompact_apply_prod E B _ _ _ _ θ hθ φ m

include hθ in
/-- The explicit formula is locally constant on the Levi. -/
theorem isLocallyConstant_normalizedAutParabolicConstantTerm
    (φ : SchwartzBruhat (GeneralLinear n E)) :
    IsLocallyConstant fun m : B.Levi E =>
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k)
          ∂(standardCompactHaar E n) ∂(standardRadicalHaar E B) := by
  have h := (normalizedAutParabolicConstantTerm E B θ hθ φ).locallyConstant
  convert h using 1
  funext m
  exact (normalizedAutParabolicConstantTerm_apply E B θ hθ φ m).symm

include hθ in
/-- The explicit formula has compact support on the Levi. -/
theorem hasCompactSupport_normalizedAutParabolicConstantTerm
    (φ : SchwartzBruhat (GeneralLinear n E)) :
    HasCompactSupport fun m : B.Levi E =>
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k)
          ∂(standardCompactHaar E n) ∂(standardRadicalHaar E B) := by
  have h := (normalizedAutParabolicConstantTerm E B θ hθ φ).hasCompactSupport
  convert h using 1
  funext m
  exact (normalizedAutParabolicConstantTerm_apply E B θ hθ φ m).symm

/-- **Evaluation with arbitrary normalized Haar measures.** For every Haar probability
measure `μK` on `K` and every Haar measure `μU` on `U` giving `U ∩ K` volume one, the
value at `m` is `δ_P(m)^{1/2} ∫ u, ∫ k, φ (k⁻¹ * m * u * θ k) dμK dμU`. -/
theorem normalizedAutParabolicConstantTerm_apply_of_isHaarMeasure
    (μK : Measure (standardMaximalCompact E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (μU : Measure (B.unipotentRadical E)) [μU.IsHaarMeasure]
    (hμU : μU {u | ((u : B.parabolic E) : GeneralLinear n E) ∈ standardMaximalCompact E n} = 1)
    (φ : SchwartzBruhat (GeneralLinear n E)) (m : B.Levi E) :
    normalizedAutParabolicConstantTerm E B θ hθ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * θ k) ∂μK ∂μU := by
  rw [eq_standardCompactHaar E n μK, eq_standardRadicalHaar E B μU hμU]
  exact normalizedAutParabolicConstantTerm_apply E B θ hθ φ m

/-- **The normalized ordinary parabolic constant term**, the case `θ = 1`. -/
def normalizedParabolicConstantTerm :
    SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E) :=
  normalizedAutParabolicConstantTerm E B (MulEquiv.refl _) continuous_id

theorem normalizedParabolicConstantTerm_eq :
    normalizedParabolicConstantTerm E B =
      normalizedAutParabolicConstantTerm E B (MulEquiv.refl _) continuous_id := rfl

/-- **Evaluation** of the normalized ordinary constant term:
`δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u k) dk du`. -/
theorem normalizedParabolicConstantTerm_apply (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    normalizedParabolicConstantTerm E B φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * k)
          ∂(standardCompactHaar E n) ∂(standardRadicalHaar E B) :=
  normalizedAutParabolicConstantTerm_apply E B (MulEquiv.refl _) continuous_id φ m

section Twisted

variable {F : Type uF} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]
  (σ : E ≃ₐ[F] E)

/-- **The normalized σ-twisted parabolic constant term**, the case
`θ = entrywiseAut σ n` (`k ↦ k^σ`, σ applied to every entry), whose continuity comes from
the `F`-module topology of `E`. -/
def normalizedTwistedParabolicConstantTerm :
    SchwartzBruhat (GeneralLinear n E) →ₗ[ℂ] SchwartzBruhat (B.Levi E) :=
  normalizedAutParabolicConstantTerm E B (entrywiseAut σ n) (continuous_entrywiseAut σ n)

theorem normalizedTwistedParabolicConstantTerm_eq :
    normalizedTwistedParabolicConstantTerm E B σ =
      normalizedAutParabolicConstantTerm E B (entrywiseAut σ n)
        (continuous_entrywiseAut σ n) := rfl

/-- **Evaluation** of the normalized σ-twisted constant term:
`δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u k^σ) dk du`. -/
theorem normalizedTwistedParabolicConstantTerm_apply (φ : SchwartzBruhat (GeneralLinear n E))
    (m : B.Levi E) :
    normalizedTwistedParabolicConstantTerm E B σ φ m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) *
        ∫ u, ∫ k, φ ((k : GeneralLinear n E)⁻¹ * B.leviEmbedding E m *
          ((u : B.parabolic E) : GeneralLinear n E) * entrywiseAut σ n k)
          ∂(standardCompactHaar E n) ∂(standardRadicalHaar E B) :=
  normalizedAutParabolicConstantTerm_apply E B _ _ φ m

end Twisted

end Standard

end LocalField

end Langlands.BaseChange
