import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Global.RankinSelberg.UnipotentClassDecomposition
import Langlands.Global.RankinSelberg.WhittakerQuotientScaling

/-! # Proof of premise B: products over the classes `unipotentIntegralClasses`

The theorem `unipotentClassProductStatement` proves `UnipotentClassProductStatement`, premise B
of the published reduction `ArchimedeanFactorizationReduction`. Through the open embedding
`classMap : 𝒩 \ 𝒢 → N_m(𝔸) \ GL_m(𝔸)` onto `unipotentIntegralClasses`, the integral is taken for
the pulled-back measure `ν₁ = comap classMap whittakerQuotientMeasure`. That measure is compared,
by the Library's uniqueness of right-invariant quotient measures, with the transport `ν₂` of the
product of the local quotient measures and of the image of Haar measure of `K^S`. Fubini then
gives the product formula. The p-adic quotient measures are moved from the canonical topology of
the completion to the completion topology. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory MeasureTheory.Measure Topology CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnipotentClass

local instance productSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance productSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- General linear groups over second countable topological rings are second countable. -/
theorem gl_secondCountable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] (n : ℕ) :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin n) R) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- Every Haar measure on a compact second countable group is right invariant. -/
theorem isMulRightInvariant_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (mu : Measure G) [IsHaarMeasure mu] : IsMulRightInvariant mu := by
  refine ⟨fun g => ?_⟩
  have hscale := isMulLeftInvariant_eq_smul (Measure.map (fun x => x * g) mu) mu
  have hm := congrArg (fun ν : Measure G => ν Set.univ) hscale
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ,
    Measure.smul_apply] at hm
  have hzero : mu Set.univ ≠ 0 := isOpen_univ.measure_ne_zero mu ⟨1, trivial⟩
  have htop : mu Set.univ ≠ ⊤ := isCompact_univ.measure_ne_top
  have he : (haarScalarFactor (Measure.map (fun x => x * g) mu) mu : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hzero htop).mp hm.symm
  rw [ENNReal.coe_eq_one.mp he, one_smul] at hscale
  exact hscale

theorem prod_ne_zero_of_ne_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (mα : Measure α) (mβ : Measure β) [SFinite mβ] (hα : mα ≠ 0) (hβ : mβ ≠ 0) :
    mα.prod mβ ≠ 0 := by
  intro h
  have h1 := congrArg (fun ν : Measure (α × β) => ν Set.univ) h
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  rw [← Set.univ_prod_univ, Measure.prod_prod] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hα (Measure.measure_univ_eq_zero.mp h2)
  · exact hβ (Measure.measure_univ_eq_zero.mp h2)

theorem pi_ne_zero_of_ne_zero {Idx : Type*} [Fintype Idx] {α : Idx → Type*}
    [∀ i, MeasurableSpace (α i)] (ms : ∀ i, Measure (α i)) [∀ i, SigmaFinite (ms i)]
    (h : ∀ i, ms i ≠ 0) : Measure.pi ms ≠ 0 := by
  intro h0
  have h1 := congrArg (fun ν : Measure (∀ i, α i) => ν Set.univ) h0
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  rw [Measure.pi_univ] at h1
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  exact h i (Measure.measure_univ_eq_zero.mp hi)

open RankinSelberg (LeftUnipotentQuotient)

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

section Proof

open Classical

variable (F : Type u) [Field F] [NumberField F] (m : ℕ) (S : Finset (FinitePlace F))

local instance awayLocalIntegralOpen :
    Fact (∀ v : {v : FinitePlace F // ¬ v ∈ S},
      IsOpen (FiniteAdelicGL.localIntegral F m v.1 : Set (FiniteLocalGL F m v.1))) :=
  ⟨fun v => (FiniteAdelicGL.localIntegral F m v.1).isOpen⟩
local instance awayTopologicalGroup : IsTopologicalGroup (AwayGL F m S) :=
  RestrictedProduct.isTopologicalGroup _
local instance awayIntegralTopologicalGroup :
    IsTopologicalGroup (awayIntegralSubgroup F m S) :=
  inferInstance
local instance semilocalTopologicalGroup : IsTopologicalGroup (SemilocalGL F m S) :=
  inferInstance
local instance semilocalT2 : T2Space (SemilocalGL F m S) :=
  (isOpenEmbedding_semilocalEmbedding F m S).isEmbedding.t2Space
local instance semilocalLocallyCompact : LocallyCompactSpace (SemilocalGL F m S) :=
  (isOpenEmbedding_semilocalEmbedding F m S).locallyCompactSpace
local instance semilocalSecondCountable : SecondCountableTopology (SemilocalGL F m S) :=
  (isOpenEmbedding_semilocalEmbedding F m S).isEmbedding.secondCountableTopology
local instance semilocalQuotientMeasurable : MeasurableSpace (SemilocalQuotient F m S) := borel _
local instance semilocalQuotientBorel : BorelSpace (SemilocalQuotient F m S) := ⟨rfl⟩
local instance semilocalQuotientT2 : T2Space (SemilocalQuotient F m S) :=
  QuotientIntegration.leftQuotient_t2Space _ (isClosed_semilocalUnipotent F m S)
local instance semilocalQuotientLocallyCompact : LocallyCompactSpace (SemilocalQuotient F m S) :=
  QuotientIntegration.leftQuotient_locallyCompactSpace _
local instance semilocalQuotientSecondCountable :
    SecondCountableTopology (SemilocalQuotient F m S) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientIntegration.leftQuotient_isOpenQuotientMap (semilocalUnipotent F m S))

theorem measurableEmbedding_classMap : MeasurableEmbedding (classMap F m S) :=
  (isOpenEmbedding_classMap F m S).measurableEmbedding

/-- The pullback `ν₁` of `whittakerQuotientMeasure` along the class map. -/
def classMeasure : Measure (SemilocalQuotient F m S) :=
  (whittakerQuotientMeasure F m).comap (classMap F m S)

/-- Integrals over `unipotentIntegralClasses` are integrals over `𝒩 \ 𝒢` for `ν₁`. -/
theorem setIntegral_unipotentIntegralClasses (f : WhittakerQuotient F m → ℂ) :
    ∫ q in unipotentIntegralClasses F m S, f q ∂whittakerQuotientMeasure F m =
      ∫ p, f (classMap F m S p) ∂classMeasure F m S := by
  rw [← range_classMap, ← (measurableEmbedding_classMap F m S).map_comap,
    (measurableEmbedding_classMap F m S).integral_map]
  rfl

theorem classMeasure_regular : (classMeasure F m S).Regular := by
  have := WhittakerQuotientScaling.regular_whittakerQuotientMeasure F m
  have : IsFiniteMeasureOnCompacts (classMeasure F m S) :=
    IsFiniteMeasureOnCompacts.comap' _ (continuous_classMap F m S)
      (measurableEmbedding_classMap F m S)
  exact Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- Nonempty open subsets of `N_m(𝔸) \ GL_m(𝔸)` have positive measure. -/
theorem whittakerQuotientMeasure_ne_zero_of_isOpen {U : Set (WhittakerQuotient F m)}
    (hU : IsOpen U) (hne : U.Nonempty) : whittakerQuotientMeasure F m U ≠ 0 := by
  have := WhittakerQuotientScaling.regular_whittakerQuotientMeasure F m
  obtain ⟨K, hK, hμK⟩ := Measure.Regular.exists_isCompact_not_null.mpr
    (WhittakerQuotientScaling.whittakerQuotientMeasure_ne_zero F m)
  obtain ⟨q, hq⟩ := hne
  obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  have hcover : K ⊆ ⋃ g : Points F m,
      LeftCosetSpace.rightTranslate (unipotentAdelic F m) g ⁻¹' U := by
    intro x _
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ x
    refine Set.mem_iUnion.mpr ⟨x⁻¹ * u, ?_⟩
    show LeftCosetSpace.rightTranslate _ (x⁻¹ * u) (LeftCosetSpace.mk _ x) ∈ U
    rw [LeftCosetSpace.rightTranslate_mk, mul_inv_cancel_left]
    exact hq
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _
    (fun g => hU.preimage (LeftCosetSpace.continuous_rightTranslate _ g)) hcover
  intro hzero
  apply hμK
  apply measure_mono_null ht
  apply (measure_biUnion_null_iff t.countable_toSet).mpr
  intro g _
  exact ((WhittakerQuotientScaling.measurePreserving_rightTranslate F m g).measure_preimage
    hU.measurableSet.nullMeasurableSet).trans hzero

theorem classMeasure_ne_zero : classMeasure F m S ≠ 0 := by
  intro h
  have h1 := congrArg (fun ν : Measure (SemilocalQuotient F m S) => ν Set.univ) h
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  rw [classMeasure, (measurableEmbedding_classMap F m S).comap_apply, Set.image_univ] at h1
  exact whittakerQuotientMeasure_ne_zero_of_isOpen F m (isOpenEmbedding_classMap F m S).isOpen_range
    ⟨_, LeftCosetSpace.mk _ 1, rfl⟩ h1

theorem classMap_rightTranslate (g : SemilocalGL F m S) (p : SemilocalQuotient F m S) :
    classMap F m S (QuotientIntegration.rightTranslate _ g p) =
      LeftCosetSpace.rightTranslate _ (semilocalEmbedding F m S g) (classMap F m S p) := by
  induction p using Quotient.inductionOn with
  | h x =>
    show LeftCosetSpace.mk _ (semilocalEmbedding F m S (x * g)) =
      LeftCosetSpace.mk _ (semilocalEmbedding F m S x * semilocalEmbedding F m S g)
    rw [map_mul]

/-- `ν₁` is invariant under right translations by the semilocal group. -/
theorem classMeasure_rightTranslate (g : SemilocalGL F m S) :
    MeasurePreserving (QuotientIntegration.rightTranslate (semilocalUnipotent F m S) g)
      (classMeasure F m S) (classMeasure F m S) := by
  have hT := (QuotientIntegration.rightTranslate (semilocalUnipotent F m S) g).continuous.measurable
  refine ⟨hT, ?_⟩
  ext s hs
  have hf := measurableEmbedding_classMap F m S
  rw [Measure.map_apply hT hs, classMeasure, hf.comap_apply, hf.comap_apply]
  have he : classMap F m S '' (QuotientIntegration.rightTranslate _ g ⁻¹' s) =
      LeftCosetSpace.rightTranslate (unipotentAdelic F m) (semilocalEmbedding F m S g) ⁻¹'
        (classMap F m S '' s) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, hp, classMap_rightTranslate F m S g p⟩
    · rintro ⟨p', hp', hq⟩
      refine ⟨QuotientIntegration.rightTranslate _ g⁻¹ p', ?_, ?_⟩
      · show QuotientIntegration.rightTranslate _ g (QuotientIntegration.rightTranslate _ g⁻¹ p') ∈ s
        rw [QuotientIntegration.rightTranslate_mul, inv_mul_cancel,
          QuotientIntegration.rightTranslate_one]
        exact hp'
      · rw [classMap_rightTranslate, hq, LeftCosetSpace.rightTranslate_mul, ← map_mul,
          mul_inv_cancel, map_one, LeftCosetSpace.rightTranslate_one]
  rw [he]
  exact (WhittakerQuotientScaling.measurePreserving_rightTranslate F m _).measure_preimage
    (hf.measurableSet_image.mpr hs).nullMeasurableSet

/-! ### Topology and measurable structures of the local factors -/

local instance realGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  gl_secondCountable ℝ n
local instance complexGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  gl_secondCountable ℂ n
local instance completionSecondCountable (v : FinitePlace F) :
    SecondCountableTopology (FiniteCompletion F v) :=
  finiteCompletion_secondCountableTopology F v
local instance completionGLSecondCountable (v : FinitePlace F) (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n (FiniteCompletion F v)) :=
  gl_secondCountable _ n
local instance realGLLocallyCompact (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact inferInstance
local instance complexGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact inferInstance
local instance completionGLLocallyCompact (v : FinitePlace F) (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n (FiniteCompletion F v)) :=
  (CompletionPadic.topologicalData v).generalLinearLocallyCompactSpace n
local instance realNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
  Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace
local instance complexNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℂ) :=
  Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace
local instance completionNLocallyCompact (v : FinitePlace F) (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n (FiniteCompletion F v)) :=
  Langlands.GeneralLinear.UpperUnipotent.locallyCompactSpace
local instance realQSecondCountable (n : ℕ) : SecondCountableTopology (LeftUnipotentQuotient n ℝ) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientIntegration.leftQuotient_isOpenQuotientMap _)
local instance complexQSecondCountable (n : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient n ℂ) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientIntegration.leftQuotient_isOpenQuotientMap _)
local instance completionQSecondCountable (v : FinitePlace F) (n : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient n (FiniteCompletion F v)) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientIntegration.leftQuotient_isOpenQuotientMap _)
local instance realQLocallyCompact (n : ℕ) : LocallyCompactSpace (LeftUnipotentQuotient n ℝ) :=
  QuotientIntegration.leftQuotient_locallyCompactSpace _
local instance complexQLocallyCompact (n : ℕ) : LocallyCompactSpace (LeftUnipotentQuotient n ℂ) :=
  QuotientIntegration.leftQuotient_locallyCompactSpace _
local instance completionQLocallyCompact (v : FinitePlace F) (n : ℕ) :
    LocallyCompactSpace (LeftUnipotentQuotient n (FiniteCompletion F v)) :=
  QuotientIntegration.leftQuotient_locallyCompactSpace _
local instance completionNMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (FiniteCompletion F v)) :=
  borel _
local instance completionNBorel (v : FinitePlace F) (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (FiniteCompletion F v)) := ⟨rfl⟩
local instance completionQMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n (FiniteCompletion F v)) := borel _
local instance completionQBorel (v : FinitePlace F) (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n (FiniteCompletion F v)) := ⟨rfl⟩

local instance semilocalMeasurable : MeasurableSpace (SemilocalGL F m S) := borel _
local instance semilocalBorel : BorelSpace (SemilocalGL F m S) := ⟨rfl⟩
local instance awayIntegralMeasurable : MeasurableSpace (awayIntegralSubgroup F m S) := borel _
local instance awayIntegralBorel : BorelSpace (awayIntegralSubgroup F m S) := ⟨rfl⟩
local instance awayIntegralSecondCountable : SecondCountableTopology (awayIntegralSubgroup F m S) :=
  ((isEmbedding_prodMkRight (1 : RealGL F m × ComplexGL F m)).comp
    (isEmbedding_prodMkRight (1 : LocalGL F m S))).secondCountableTopology
local instance awayIntegralT2 : T2Space (awayIntegralSubgroup F m S) :=
  ((isEmbedding_prodMkRight (1 : RealGL F m × ComplexGL F m)).comp
    (isEmbedding_prodMkRight (1 : LocalGL F m S))).t2Space
local instance awayIntegralCompact : CompactSpace (awayIntegralSubgroup F m S) :=
  isCompact_iff_compactSpace.mp (isCompact_awayIntegral F m S)

theorem isClosed_awayUnipotent :
    IsClosed (awayUnipotent F m S : Set (awayIntegralSubgroup F m S)) := by
  have hc : Continuous (fun k : awayIntegralSubgroup F m S =>
      ((1 : RealGL F m × ComplexGL F m), ((1 : LocalGL F m S), k))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  convert (isClosed_semilocalUnipotent F m S).preimage hc using 1
  ext k
  constructor
  · intro hk
    exact ⟨⟨fun v _ => Subgroup.one_mem _, fun v _ => Subgroup.one_mem _⟩,
      fun v _ => Subgroup.one_mem _, hk⟩
  · intro h
    exact h.2.2

local instance awayIntegralLocallyCompact : LocallyCompactSpace (awayIntegralSubgroup F m S) :=
  isCompact_univ.locallyCompactSpace_of_mem_nhds_of_group (x := 1) Filter.univ_mem
local instance awayUnipotentCompact : CompactSpace (awayUnipotent F m S) :=
  isCompact_iff_compactSpace.mp (isClosed_awayUnipotent F m S).isCompact
local instance awayUnipotentTopologicalGroup : IsTopologicalGroup (awayUnipotent F m S) :=
  inferInstance
local instance awayUnipotentT2 : T2Space (awayUnipotent F m S) :=
  Topology.IsEmbedding.subtypeVal.t2Space
local instance awayUnipotentSecondCountable : SecondCountableTopology (awayUnipotent F m S) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance awayUnipotentLocallyCompact : LocallyCompactSpace (awayUnipotent F m S) :=
  (isClosed_awayUnipotent F m S).isClosedEmbedding_subtypeVal.locallyCompactSpace
local instance awayUnipotentMeasurable : MeasurableSpace (awayUnipotent F m S) := inferInstance
local instance awayUnipotentBorel : BorelSpace (awayUnipotent F m S) := inferInstance
local instance awayQuotientMeasurable :
    MeasurableSpace (QuotientIntegration.LeftQuotient (awayUnipotent F m S)) := borel _
local instance awayQuotientBorel :
    BorelSpace (QuotientIntegration.LeftQuotient (awayUnipotent F m S)) := ⟨rfl⟩
local instance awayQuotientSecondCountable :
    SecondCountableTopology (QuotientIntegration.LeftQuotient (awayUnipotent F m S)) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (QuotientIntegration.leftQuotient_isOpenQuotientMap _)
local instance unipotentLocallyCompact : LocallyCompactSpace (semilocalUnipotent F m S) :=
  (isClosed_semilocalUnipotent F m S).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-! ### Unimodularity of `𝒩` -/

/-- `𝒩` is the product of its local factors, as a topological group. -/
def unipotentProductEquiv : semilocalUnipotent F m S ≃ₜ*
    ((∀ _ : {v : InfinitePlace F // v.IsReal}, Langlands.GeneralLinear.upperUnipotent m ℝ) ×
      (∀ _ : {v : InfinitePlace F // v.IsComplex}, Langlands.GeneralLinear.upperUnipotent m ℂ)) ×
    ((∀ v : S, Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1)) ×
      awayUnipotent F m S) :=
  (QuotientIntegration.prodSubgroupHomeomorph _ _).trans
    (prodCongr
      ((QuotientIntegration.prodSubgroupHomeomorph _ _).trans
        (prodCongr (QuotientIntegration.piSubgroupHomeomorph _)
          (QuotientIntegration.piSubgroupHomeomorph _)))
      ((QuotientIntegration.prodSubgroupHomeomorph _ _).trans
        (prodCongr (QuotientIntegration.piSubgroupHomeomorph _) (ContinuousMulEquiv.refl _))))

/-- A right-invariant Haar measure on the unipotent group over a finite completion. -/
def completionUnipotentHaar (v : FinitePlace F) (t : ℕ) :
    Measure (Langlands.GeneralLinear.upperUnipotent (t + 1) (FiniteCompletion F v)) :=
  letI := (CompletionPadic.topologicalData v).valuativeRel
  haveI : IsNonarchimedeanLocalField (FiniteCompletion F v) :=
    (CompletionPadic.topologicalData v).localField
  RankinSelberg.unipotentHaar _ t

theorem completionUnipotentHaar_isHaar (v : FinitePlace F) (t : ℕ) :
    IsHaarMeasure (completionUnipotentHaar F v t) := by
  let := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (FiniteCompletion F v) :=
    (CompletionPadic.topologicalData v).localField
  exact RankinSelberg.unipotentHaar_isHaar _ t

theorem completionUnipotentHaar_rightInvariant (v : FinitePlace F) (t : ℕ) :
    IsMulRightInvariant (completionUnipotentHaar F v t) := by
  let := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (FiniteCompletion F v) :=
    (CompletionPadic.topologicalData v).localField
  exact RankinSelberg.unipotentHaar_isMulRightInvariant _ t

variable (t : ℕ)

/-- Haar measure on `𝒩` is right invariant. -/
theorem semilocalUnipotent_haar_rightInvariant
    (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t)
    (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t) :
    IsMulRightInvariant (Measure.haar : Measure (semilocalUnipotent F (t + 1) S)) := by
  have : ∀ v, IsHaarMeasure (DR v).unipotentHaar := fun v => (DR v).unipotentHaar_isHaar
  have : ∀ v, IsMulRightInvariant (DR v).unipotentHaar :=
    fun v => (DR v).unipotentHaar_rightInvariant
  have : ∀ v, IsHaarMeasure (DC v).unipotentHaar := fun v => (DC v).unipotentHaar_isHaar
  have : ∀ v, IsMulRightInvariant (DC v).unipotentHaar :=
    fun v => (DC v).unipotentHaar_rightInvariant
  have : ∀ v : S, IsHaarMeasure (completionUnipotentHaar F v.1 t) :=
    fun v => completionUnipotentHaar_isHaar F v.1 t
  have : ∀ v : S, IsMulRightInvariant (completionUnipotentHaar F v.1 t) :=
    fun v => completionUnipotentHaar_rightInvariant F v.1 t
  have : IsMulRightInvariant (Measure.haar : Measure (awayUnipotent F (t + 1) S)) :=
    isMulRightInvariant_of_compactSpace _
  have h1 : IsHaarMeasure (Measure.pi fun v => (DR v).unipotentHaar) := inferInstance
  have h2 : IsHaarMeasure (Measure.pi fun v => (DC v).unipotentHaar) := inferInstance
  have h3 : IsHaarMeasure (Measure.pi fun v : S => completionUnipotentHaar F v.1 t) :=
    inferInstance
  have d1 : SFinite (Measure.pi fun v => (DR v).unipotentHaar) := inferInstance
  have d2 : SFinite (Measure.pi fun v => (DC v).unipotentHaar) := inferInstance
  have d3 : MeasurableMul (∀ _ : {v : InfinitePlace F // v.IsReal},
    Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) := inferInstance
  have d4 : MeasurableMul (∀ _ : {v : InfinitePlace F // v.IsComplex},
    Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ) := inferInstance
  have h4 : IsHaarMeasure ((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)) := prod.instIsHaarMeasure _ _
  have h5 : IsHaarMeasure ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
      (Measure.haar : Measure (awayUnipotent F (t + 1) S))) := inferInstance
  have d5 : SFinite ((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)) := inferInstance
  have d6 : SFinite ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
      (Measure.haar : Measure (awayUnipotent F (t + 1) S))) := inferInstance
  have d7 : MeasurableMul ((∀ _ : {v : InfinitePlace F // v.IsReal},
    Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) × (∀ _ : {v : InfinitePlace F // v.IsComplex},
    Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ)) := inferInstance
  have d8 : MeasurableMul ((∀ v : S, Langlands.GeneralLinear.upperUnipotent (t + 1)
    (FiniteCompletion F v.1)) × awayUnipotent F (t + 1) S) := inferInstance
  have h6 : IsHaarMeasure (((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)).prod
      ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
        (Measure.haar : Measure (awayUnipotent F (t + 1) S)))) := prod.instIsHaarMeasure _ _
  have r1 : IsMulRightInvariant ((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)) := Measure.prod.instIsMulRightInvariant
  have r2 : IsMulRightInvariant ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
      (Measure.haar : Measure (awayUnipotent F (t + 1) S))) := Measure.prod.instIsMulRightInvariant
  have r3 : IsMulRightInvariant (((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)).prod
      ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
        (Measure.haar : Measure (awayUnipotent F (t + 1) S)))) :=
    Measure.prod.instIsMulRightInvariant
  exact QuotientIntegration.isMulRightInvariant_of_continuousMulEquiv
    (unipotentProductEquiv F (t + 1) S)
    (((Measure.pi fun v => (DR v).unipotentHaar).prod
      (Measure.pi fun v => (DC v).unipotentHaar)).prod
      ((Measure.pi fun v : S => completionUnipotentHaar F v.1 t).prod
        (Measure.haar : Measure (awayUnipotent F (t + 1) S)))) _

/-! ### Coordinates on `𝒩 \ 𝒢` and the product measure -/

/-- The product of the local quotients and of `Y = (K^S ∩ N) \ K^S`. -/
abbrev Coordinates :=
  ((∀ _ : {v : InfinitePlace F // v.IsReal},
      QuotientIntegration.LeftQuotient (Langlands.GeneralLinear.upperUnipotent m ℝ)) ×
    (∀ _ : {v : InfinitePlace F // v.IsComplex},
      QuotientIntegration.LeftQuotient (Langlands.GeneralLinear.upperUnipotent m ℂ))) ×
  ((∀ v : S, QuotientIntegration.LeftQuotient
      (Langlands.GeneralLinear.upperUnipotent m (FiniteCompletion F v.1))) ×
    QuotientIntegration.LeftQuotient (awayUnipotent F m S))

/-- The coordinates `Θ : 𝒩 \ 𝒢 ≃ₜ (∏ Q_v × ∏ Q_w) × (∏_S Q_v × Y)`. -/
def quotientCoordinates : SemilocalQuotient F m S ≃ₜ Coordinates F m S :=
  (QuotientIntegration.leftQuotientProdHomeomorph _ _).trans
    (Homeomorph.prodCongr
      ((QuotientIntegration.leftQuotientProdHomeomorph _ _).trans
        (Homeomorph.prodCongr (QuotientIntegration.leftQuotientPiHomeomorph _)
          (QuotientIntegration.leftQuotientPiHomeomorph _)))
      ((QuotientIntegration.leftQuotientProdHomeomorph _ _).trans
        (Homeomorph.prodCongr (QuotientIntegration.leftQuotientPiHomeomorph _)
          (Homeomorph.refl _))))

theorem quotientCoordinates_mk (x : SemilocalGL F m S) :
    quotientCoordinates F m S (LeftCosetSpace.mk _ x) =
      (((fun v => LeftCosetSpace.mk _ (x.1.1 v)), fun v => LeftCosetSpace.mk _ (x.1.2 v)),
        ((fun v => LeftCosetSpace.mk _ (x.2.1 v)), LeftCosetSpace.mk _ x.2.2)) :=
  rfl

theorem quotientCoordinates_rightTranslate (g : SemilocalGL F m S)
    (q : SemilocalQuotient F m S) :
    quotientCoordinates F m S (QuotientIntegration.rightTranslate _ g q) =
      Prod.map
        (Prod.map (fun a v => QuotientIntegration.rightTranslate _ (g.1.1 v) (a v))
          (fun a v => QuotientIntegration.rightTranslate _ (g.1.2 v) (a v)))
        (Prod.map (fun a v => QuotientIntegration.rightTranslate _ (g.2.1 v) (a v))
          (QuotientIntegration.rightTranslate _ g.2.2))
        (quotientCoordinates F m S q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- `ρ_Y`: the image in `Y` of Haar measure on the compact group `K^S`. -/
def awayQuotientMeasure : Measure (QuotientIntegration.LeftQuotient (awayUnipotent F m S)) :=
  Measure.map (QuotientIntegration.leftQuotientMap _)
    (Measure.haar : Measure (awayIntegralSubgroup F m S))

theorem measurable_awayQuotientMap :
    Measurable (QuotientIntegration.leftQuotientMap (awayUnipotent F m S)) :=
  (QuotientIntegration.leftQuotient_isOpenQuotientMap _).continuous.measurable

theorem awayQuotientMeasure_rightTranslate (k : awayIntegralSubgroup F m S) :
    MeasurePreserving (QuotientIntegration.rightTranslate (awayUnipotent F m S) k)
      (awayQuotientMeasure F m S) (awayQuotientMeasure F m S) := by
  have : IsMulRightInvariant (Measure.haar : Measure (awayIntegralSubgroup F m S)) :=
    isMulRightInvariant_of_compactSpace _
  have hq := measurable_awayQuotientMap F m S
  have hT := (QuotientIntegration.rightTranslate (awayUnipotent F m S) k).continuous.measurable
  refine ⟨hT, ?_⟩
  rw [awayQuotientMeasure, Measure.map_map hT hq]
  have hc : (QuotientIntegration.rightTranslate (awayUnipotent F m S) k) ∘
      QuotientIntegration.leftQuotientMap _ =
      QuotientIntegration.leftQuotientMap _ ∘ (fun x => x * k) :=
    funext fun x => rfl
  rw [hc, ← Measure.map_map hq (measurable_mul_const k), map_mul_right_eq_self]

theorem awayQuotientMeasure_univ :
    awayQuotientMeasure F m S Set.univ =
      (Measure.haar : Measure (awayIntegralSubgroup F m S)) Set.univ := by
  rw [awayQuotientMeasure, Measure.map_apply (measurable_awayQuotientMap F m S)
    MeasurableSet.univ, Set.preimage_univ]

theorem awayQuotientMeasure_univ_toReal_pos :
    0 < (awayQuotientMeasure F m S Set.univ).toReal := by
  rw [awayQuotientMeasure_univ]
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ ⟨1, trivial⟩)
    isCompact_univ.measure_ne_top

instance awayQuotientMeasure_isFinite : IsFiniteMeasure (awayQuotientMeasure F m S) := by
  rw [awayQuotientMeasure]
  infer_instance

local instance awayQuotientLocallyCompact :
    LocallyCompactSpace (QuotientIntegration.LeftQuotient (awayUnipotent F m S)) :=
  QuotientIntegration.leftQuotient_locallyCompactSpace _

/-- The product measure `P` on the coordinates. -/
def productMeasure
    (mR : {v : InfinitePlace F // v.IsReal} → Measure (LeftUnipotentQuotient t ℝ))
    (mC : {v : InfinitePlace F // v.IsComplex} → Measure (LeftUnipotentQuotient t ℂ))
    (mS : ∀ v : S, Measure (LeftUnipotentQuotient t (FiniteCompletion F v.1))) :
    Measure (Coordinates F (t + 1) S) :=
  ((Measure.pi mR).prod (Measure.pi mC)).prod
    ((Measure.pi mS).prod (awayQuotientMeasure F (t + 1) S))

theorem realQuotientProjection_classMap_eq (p : SemilocalQuotient F (t + 1) S)
    (v : {v : InfinitePlace F // v.IsReal}) :
    realQuotientProjection F t v (classMap F (t + 1) S p) =
      (quotientCoordinates F (t + 1) S p).1.1 v := by
  induction p using Quotient.inductionOn with
  | h x => exact realQuotientProjection_classMap F S t x v

theorem complexQuotientProjection_classMap_eq (p : SemilocalQuotient F (t + 1) S)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    complexQuotientProjection F t v (classMap F (t + 1) S p) =
      (quotientCoordinates F (t + 1) S p).1.2 v := by
  induction p using Quotient.inductionOn with
  | h x => exact complexQuotientProjection_classMap F S t x v

theorem finiteQuotientProjection_classMap_eq (p : SemilocalQuotient F (t + 1) S) (v : S) :
    finiteQuotientProjection F t v.1 (classMap F (t + 1) S p) =
      ((quotientCoordinates F (t + 1) S p).2.1 v :
        LeftUnipotentQuotient t (CompletionPadic.padicField v.1).Carrier) := by
  induction p using Quotient.inductionOn with
  | h x => exact finiteQuotientProjection_classMap F S t x v

/-- **Core of premise B**, with quotient measures at the places of `S` for the completion
topology. -/
theorem unipotentClassProduct_core
    (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t)
    (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t)
    (mS : ∀ v : S, Measure (LeftUnipotentQuotient t (FiniteCompletion F v.1)))
    (hS0 : ∀ v, mS v ≠ 0) (hSreg : ∀ v, (mS v).Regular)
    (hSinv : ∀ v g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) (mS v) (mS v)) :
    ∃ C : ℂ, C ≠ 0 ∧
      ∀ (fR : {v : InfinitePlace F // v.IsReal} → LeftUnipotentQuotient t ℝ → ℂ)
        (fC : {v : InfinitePlace F // v.IsComplex} → LeftUnipotentQuotient t ℂ → ℂ)
        (fS : ∀ v : S, LeftUnipotentQuotient t (CompletionPadic.padicField v.1).Carrier → ℂ),
        ∫ q in unipotentIntegralClasses F (t + 1) S,
            (∏ v, fR v (realQuotientProjection F t v q)) *
              (∏ w, fC w (complexQuotientProjection F t w q)) *
              ∏ v : S, fS v (finiteQuotientProjection F t v.1 q)
            ∂whittakerQuotientMeasure F (t + 1) =
          C * (∏ v, ∫ y, fR v y ∂(DR v).measure) * (∏ w, ∫ y, fC w y ∂(DC w).measure) *
            ∏ v : S, ∫ y, fS v y ∂(mS v) := by
  -- local finiteness of the local quotient measures
  have : ∀ v, IsMulRightInvariant (DR v).unipotentHaar :=
    fun v => (DR v).unipotentHaar_rightInvariant
  have : ∀ v, IsMulRightInvariant (DC v).unipotentHaar :=
    fun v => (DC v).unipotentHaar_rightInvariant
  have : IsFiniteMeasure (awayQuotientMeasure F (t + 1) S) := awayQuotientMeasure_isFinite F (t + 1) S
  have : IsLocallyFiniteMeasure (awayQuotientMeasure F (t + 1) S) :=
    ⟨fun _ => ⟨Set.univ, Filter.univ_mem, measure_lt_top _ _⟩⟩
  have : ∀ v, (DR v).measure.Regular := fun v => (DR v).compatible.regular
  have : ∀ v, (DC v).measure.Regular := fun v => (DC v).compatible.regular
  have : ∀ v, (mS v).Regular := hSreg
  have : ∀ v, SigmaFinite (DR v).measure := fun v => inferInstance
  have : ∀ v, SigmaFinite (DC v).measure := fun v => inferInstance
  have : ∀ v, SigmaFinite (mS v) := fun v => inferInstance
  set P := productMeasure F S t (fun v => (DR v).measure) (fun v => (DC v).measure) mS with hP
  have hY0 : awayQuotientMeasure F (t + 1) S ≠ 0 := by
    intro h
    have h1 := awayQuotientMeasure_univ_toReal_pos F (t + 1) S
    rw [h] at h1
    simp at h1
  have hP0 : P ≠ 0 :=
    prod_ne_zero_of_ne_zero _ _
      (prod_ne_zero_of_ne_zero _ _
        (pi_ne_zero_of_ne_zero _ fun v => (DR v).compatible.nonzero)
        (pi_ne_zero_of_ne_zero _ fun v => (DC v).compatible.nonzero))
      (prod_ne_zero_of_ne_zero _ _ (pi_ne_zero_of_ne_zero _ hS0) hY0)
  have : IsLocallyFiniteMeasure P := by
    rw [hP, productMeasure]
    infer_instance
  set e := (quotientCoordinates F (t + 1) S).toMeasurableEquiv with he
  set ν₂ := Measure.map e.symm P with hν₂
  have : IsFiniteMeasureOnCompacts ν₂ :=
    IsFiniteMeasureOnCompacts.map P (quotientCoordinates F (t + 1) S).symm
  have : ν₂.Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hν₂0 : ν₂ ≠ 0 :=
    (Measure.map_ne_zero_iff e.symm.measurable.aemeasurable).mpr hP0
  have hν₂inv : ∀ g, MeasurePreserving
      (QuotientIntegration.rightTranslate (semilocalUnipotent F (t + 1) S) g) ν₂ ν₂ := by
    intro g
    refine QuotientIntegration.measurePreserving_map_symm_of_conj e P
      (QuotientIntegration.rightTranslate _ g).continuous.measurable
      (fun q => quotientCoordinates_rightTranslate F (t + 1) S g q) ?_
    exact ((measurePreserving_pi _ _ fun v => (DR v).compatible.right_invariant (g.1.1 v)).prod
        (measurePreserving_pi _ _ fun v => (DC v).compatible.right_invariant (g.1.2 v))).prod
      ((measurePreserving_pi _ _ fun v => hSinv v (g.2.1 v)).prod
        (awayQuotientMeasure_rightTranslate F (t + 1) S g.2.2))
  have := semilocalUnipotent_haar_rightInvariant F S t DR DC
  have := classMeasure_regular F (t + 1) S
  obtain ⟨c, hc, hν⟩ := QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient
    (semilocalUnipotent F (t + 1) S) (isClosed_semilocalUnipotent F (t + 1) S) Measure.haar
    (classMeasure F (t + 1) S) ν₂ (classMeasure_ne_zero F (t + 1) S) hν₂0
    (classMeasure_rightTranslate F (t + 1) S) hν₂inv
  refine ⟨((c * (awayQuotientMeasure F (t + 1) S Set.univ).toReal : ℝ) : ℂ), ?_,
    fun fR fC fS => ?_⟩
  · have h := mul_pos hc (awayQuotientMeasure_univ_toReal_pos F (t + 1) S)
    exact_mod_cast h.ne'
  have key : ∀ f : WhittakerQuotient F (t + 1) → ℂ,
      ∫ q in unipotentIntegralClasses F (t + 1) S, f q ∂whittakerQuotientMeasure F (t + 1) =
        (c : ℂ) * ∫ z, f (classMap F (t + 1) S (e.symm z)) ∂P := by
    intro f
    rw [setIntegral_unipotentIntegralClasses, hν, integral_smul_measure,
      ENNReal.toReal_ofReal hc.le, Complex.real_smul, hν₂, integral_map_equiv]
  rw [key]
  have hΦ : ∀ z : Coordinates F (t + 1) S,
      (∏ v, fR v (realQuotientProjection F t v (classMap F (t + 1) S (e.symm z)))) *
          (∏ w, fC w (complexQuotientProjection F t w (classMap F (t + 1) S (e.symm z)))) *
          ∏ v : S, fS v (finiteQuotientProjection F t v.1 (classMap F (t + 1) S (e.symm z))) =
        ((∏ v, fR v (z.1.1 v)) * ∏ w, fC w (z.1.2 w)) * ((∏ v : S, fS v (z.2.1 v)) * 1) := by
    intro z
    have hz : quotientCoordinates F (t + 1) S (e.symm z) = z :=
      (quotientCoordinates F (t + 1) S).apply_symm_apply z
    rw [mul_one]
    simp only [realQuotientProjection_classMap_eq, complexQuotientProjection_classMap_eq,
      finiteQuotientProjection_classMap_eq, hz]
  rw [integral_congr_ae (Filter.Eventually.of_forall hΦ), hP, productMeasure,
    integral_prod_mul
      (fun a : (∀ _ : {v : InfinitePlace F // v.IsReal}, LeftUnipotentQuotient t ℝ) ×
          (∀ _ : {v : InfinitePlace F // v.IsComplex}, LeftUnipotentQuotient t ℂ) =>
        (∏ v, fR v (a.1 v)) * ∏ w, fC w (a.2 w))
      (fun b : (∀ v : S, LeftUnipotentQuotient t (FiniteCompletion F v.1)) ×
          QuotientIntegration.LeftQuotient (awayUnipotent F (t + 1) S) =>
        (∏ v : S, fS v (b.1 v)) * 1),
    integral_prod_mul (fun x : ∀ _ : {v : InfinitePlace F // v.IsReal}, LeftUnipotentQuotient t ℝ =>
        ∏ v, fR v (x v))
      (fun y : ∀ _ : {v : InfinitePlace F // v.IsComplex}, LeftUnipotentQuotient t ℂ =>
        ∏ w, fC w (y w)),
    integral_prod_mul (fun x : ∀ v : S, LeftUnipotentQuotient t (FiniteCompletion F v.1) =>
        ∏ v : S, fS v (x v))
      (fun _ : QuotientIntegration.LeftQuotient (awayUnipotent F (t + 1) S) => (1 : ℂ)),
    integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod,
    integral_fintype_prod_eq_prod, integral_const, Measure.real, Complex.real_smul, mul_one]
  push_cast
  ring

end Proof

/-! ### From the canonical topology to the completion topology -/

/-- A nonzero regular right-invariant measure on `N_(n+1)(K) \ GL_(n+1)(K)` whose integrals are
given by `c`. -/
abbrev QuotientMeasureFacts (K : Type*) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (c : (LeftUnipotentQuotient n K → ℂ) → ℂ) : Prop :=
  letI := borel (LeftUnipotentQuotient n K)
  ∃ mu : Measure (LeftUnipotentQuotient n K), mu ≠ 0 ∧ mu.Regular ∧
    (∀ g, MeasurePreserving (QuotientIntegration.rightTranslate _ g) mu mu) ∧
    ∀ f, ∫ y, f y ∂mu = c f

/-- `QuotientMeasureFacts` only depends on the topology of the field. -/
theorem quotientMeasureFacts_congr {K : Type*} [Field K] {τ₁ τ₂ : TopologicalSpace K}
    (h : τ₁ = τ₂) (hR₁ : @IsTopologicalRing K τ₁ _) (hR₂ : @IsTopologicalRing K τ₂ _) (n : ℕ)
    (c : (LeftUnipotentQuotient n K → ℂ) → ℂ) (H : @QuotientMeasureFacts K _ τ₂ hR₂ n c) :
    @QuotientMeasureFacts K _ τ₁ hR₁ n c := by
  cases h
  exact H

/-- A compatible quotient measure at a finite place, for the canonical topology of the
completion, gives a nonzero regular right-invariant measure for the completion topology with
the same integrals. -/
theorem exists_completion_quotientMeasure {F : Type u} [Field F] [NumberField F] (t : ℕ)
    (v : FinitePlace F) (mu : PadicQuotientMeasure (CompletionPadic.padicField v) t)
    (hmu : IsCompatiblePadicQuotientMeasure (CompletionPadic.padicField v) mu) :
    QuotientMeasureFacts (FiniteCompletion F v) t
      (fun f => padicQuotientIntegral (CompletionPadic.padicField v) mu f) := by
  have hR : @IsTopologicalRing (FiniteCompletion F v)
      (CompletionPadic.padicField v).canonicalTopologicalData.topology _ := by
    rw [← CompletionPadic.completion_topology_eq v]
    exact inferInstanceAs (IsTopologicalRing (FiniteCompletion F v))
  refine quotientMeasureFacts_congr (CompletionPadic.completion_topology_eq v) _ hR t _ ?_
  obtain ⟨_, h0, hreg, hinv, -, -⟩ := hmu
  exact ⟨mu, h0, hreg, hinv, fun f => rfl⟩

open Classical in
/-- **Proof of premise B** (`UnipotentClassProductStatement`). -/
theorem unipotentClassProductStatement : UnipotentClassProductStatement.{u} := by
  intro F _ _ t S DR DC μS hμS
  choose mS hS0 hSreg hSinv hSint using fun v : S =>
    exists_completion_quotientMeasure t v.1 (μS v) (hμS v)
  obtain ⟨C, hC, h⟩ := unipotentClassProduct_core F S t DR DC mS hS0 hSreg hSinv
  refine ⟨C, hC, fun fR fC fS => ?_⟩
  rw [h fR fC fS]
  simp only [hSint]

end Langlands.Global.RankinSelbergGlobal.UnipotentClass
