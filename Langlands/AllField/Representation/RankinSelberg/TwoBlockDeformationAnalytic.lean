import Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationFlat
/-!
# The deformed Whittaker coefficients of flat sections are entire
-/

noncomputable section

open MeasureTheory Topology Filter

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding FlatCoefficientDifferentiable blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos character_eq_one_mem_nhds compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule deformedAverage determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_deformedAverage_formula exists_deformedAverage_mem exists_deformed_section_jacquetFunction_one_ne_zero exists_matrix_exhaustion exists_mem_unipotentExhaustion exists_oppositeParabolic_mul exists_section_jacquetFunction_one_ne_zero exists_uniform_stabilizer exists_upperUnipotent_exhaustion flatCoefficientDifferentiable flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen functional_deformedAverage inducedRep_flatSection_of_mem inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inv_smul_inducedRep_flatSection_of_mem inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isCompact_unipotentExhaustion isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm isOpen_ker_inverseStandardCharacter isSmooth_twoBlockDeformedBlocks jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower monotone_unipotentExhaustion oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer sectionEval_sum tensorContraction_blockTensor unipotentExhaustion
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet

universe uF uW

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)

/-- The analytic conclusion: for inverse-character functionals `J_u` on `ρ_u` that agree
with JPSS (4.6.2) at the identity on the compact-radical sections, where the latter
together with the character relations span `ρ_u`, every coefficient
`u ↦ J_u(ρ_u(g) f_u)` of a flat family is entire. -/
def FlatCoefficientDifferentiable : Prop :=
  ∀ [MeasurableSpace F] (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    [OpensMeasurableSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [IsFiniteMeasureOnCompacts μ]
    (J : ∀ u : ℂ, glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u)),
    (∀ (u : ℂ) (f : Sections F h (twoBlockDeformedBlocks F m σ u)),
      f ∈ compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) →
        (J u).val f = jacquetFunction ψ ell μ f 1) →
    (∀ u : ℂ, Jacquet.Localization.relations (twoBlockDeformedInduced F m h σ u)
        (upperUnipotent (t + 1) F) (inverseStandardCharacter ψ t) ⊔
      compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) = ⊤) →
    ∀ (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0)) (g : GeneralLinear (t + 1) F),
      Differentiable ℂ (fun u : ℂ =>
        (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)))

section Average

/-- A chosen increasing exhaustion of the upper unipotent group by compact open subgroups. -/
def unipotentExhaustion (n : ℕ) :
    ℕ → OpenSubgroup (upperUnipotent n F) :=
  Classical.choose (exists_upperUnipotent_exhaustion F n)

theorem isCompact_unipotentExhaustion (n k : ℕ) :
    IsCompact (unipotentExhaustion F n k : Set (upperUnipotent n F)) :=
  (Classical.choose_spec (exists_upperUnipotent_exhaustion F n)).1 k

theorem monotone_unipotentExhaustion (n : ℕ) :
    Monotone (unipotentExhaustion F n) :=
  (Classical.choose_spec (exists_upperUnipotent_exhaustion F n)).2.1

theorem exists_mem_unipotentExhaustion (n : ℕ) :
    ∀ g : upperUnipotent n F, ∃ k, g ∈ unipotentExhaustion F n k :=
  (Classical.choose_spec (exists_upperUnipotent_exhaustion F n)).2.2

/-- Evaluation of a finite sum of sections. -/
theorem sectionEval_sum {σ' : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
    {ι : Type*} (s : Finset ι) (f : ι → Sections F h σ') (y : GeneralLinear (t + 1) F) :
    sectionEval F h σ' (∑ i ∈ s, f i) y = ∑ i ∈ s, sectionEval F h σ' (f i) y := by
  let L : Sections F h σ' →ₗ[ℂ] PiTensorProduct ℂ W :=
    { toFun := fun f => sectionEval F h σ' f y
      map_add' := fun f f' => sectionEval_add f f' y
      map_smul' := fun c f => sectionEval_smul c f y }
  exact map_sum L f s

/-- The `ψ⁻¹`-twisted average of `ρ_u` over the `k`-th subgroup of the exhaustion. -/
def deformedAverage (u : ℂ) (k : ℕ) :
    Sections F h (twoBlockDeformedBlocks F m σ u) →ₗ[ℂ]
      Sections F h (twoBlockDeformedBlocks F m σ u) :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  Jacquet.Localization.characterAverage
    ((⟨⟩ : LocalFieldData F).isSmooth_normalizedOppositeParabolicInduced (succBlockShape m h)
      ((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u)))
    (isOpen_ker_inverseStandardCharacter F ψ t)
    (unipotentExhaustion F (t + 1) k) (isCompact_unipotentExhaustion F (t + 1) k)

/-- Inverse-character functionals are unchanged by the averages. -/
theorem functional_deformedAverage (u : ℂ) (k : ℕ) :
    ∀ (ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u))
      (f : Sections F h (twoBlockDeformedBlocks F m σ u)),
      ℓ.val (deformedAverage F h σ ψ u k f) = ℓ.val f := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  intro ℓ f
  exact Jacquet.Localization.functional_characterAverage _ _ _ _ ℓ f

/-- If the character relations and the compact-radical sections span `ρ_u`, every section
is averaged into the compact-radical sections far enough along the exhaustion. -/
theorem exists_deformedAverage_mem (u : ℂ) :
    Jacquet.Localization.relations (twoBlockDeformedInduced F m h σ u)
        (upperUnipotent (t + 1) F) (inverseStandardCharacter ψ t) ⊔
      compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) = ⊤ →
    ∀ f : Sections F h (twoBlockDeformedBlocks F m σ u), ∃ k,
      deformedAverage F h σ ψ u k f ∈ compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  intro htop f
  obtain ⟨k, hk⟩ := Jacquet.Localization.eventually_characterAverage_mem
    ((⟨⟩ : LocalFieldData F).isSmooth_normalizedOppositeParabolicInduced (succBlockShape m h)
      ((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u)))
    (isOpen_ker_inverseStandardCharacter F ψ t)
    (unipotentExhaustion F (t + 1)) (isCompact_unipotentExhaustion F (t + 1))
    (monotone_unipotentExhaustion F (t + 1)) (exists_mem_unipotentExhaustion F (t + 1))
    (compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u))
    (fun n v hv => inducedRep_mem_compactRadicalSubmodule F h _ n hv) htop f
  exact ⟨k, hk k le_rfl⟩

/-- A translate `ρ_u(g) f_u` of a flat section is fixed by every `n` whose conjugate
`g⁻¹ n g` lies in the uniform stabilizer of `f`. -/
theorem inducedRep_flatSection_of_mem (u : ℂ) (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (g : GeneralLinear (t + 1) F) {n : GeneralLinear (t + 1) F}
    (hn : g⁻¹ * n * g ∈ flatStabilizer F h σ v₀) :
    twoBlockDeformedInduced F m h σ u n
        (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) =
      twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change flatFunction F h σ u v₀ (x * n * g) = flatFunction F h σ u v₀ (x * g)
  have hx : x * n * g = x * g * (g⁻¹ * n * g) := by group
  rw [hx]
  exact flatFunction_mul_flatStabilizer F h σ u v₀ (x * g) hn

/-- The twisted form of `inducedRep_flatSection_of_mem` for a trivial character value. -/
theorem inv_smul_inducedRep_flatSection_of_mem (u : ℂ)
    (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0)) (g : GeneralLinear (t + 1) F)
    {n : GeneralLinear (t + 1) F} {z : ℂˣ} (hz : z = 1)
    (hn : MulAut.conj g⁻¹ n ∈ flatStabilizer F h σ v₀) :
    (z : ℂ)⁻¹ • twoBlockDeformedInduced F m h σ u n
        (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) =
      twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀) := by
  rw [MulAut.conj_apply, inv_inv] at hn
  rw [hz, Units.val_one, inv_one, one_smul]
  exact inducedRep_flatSection_of_mem F h σ u v₀ g hn

/-- The average of a translated flat family is a finite exponential sum in `u` with
`u`-independent coefficients: `(P_k ρ_u(g) f_u)(y) = ∑_i κ(y d_i)^u a_i f(y d_i)`. The
coset representatives come from one finite-index subgroup of the `k`-th subgroup which
fixes `ρ_u(g) f_u` for every `u` and lies in the kernel of the character. -/
theorem exists_deformedAverage_formula (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (g : GeneralLinear (t + 1) F) (k : ℕ) :
    ∃ (ι : Type uF) (_ : Fintype ι) (d : ι → GeneralLinear (t + 1) F) (a : ι → ℂ),
      ∀ (u : ℂ) (y : GeneralLinear (t + 1) F),
        sectionEval F h _ (deformedAverage F h σ ψ u k
            (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀))) y =
          ∑ i, ((blockZeroNorm F h (y * d i) : ℂ) ^ u) •
            (a i • sectionEval F h _ v₀ (y * d i)) := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1)
  let N := upperUnipotent (t + 1) F
  let χ := inverseStandardCharacter ψ t
  let H := unipotentExhaustion F (t + 1) k
  have : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_unipotentExhaustion F (t + 1) k)
  let K₁ := flatStabilizer F h σ v₀
  let φ : H →* GeneralLinear (t + 1) F :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (N.subtype.comp (H : Subgroup N).subtype)
  have hφ : Continuous φ := by
    change Continuous fun x : H => g⁻¹ * ((x : N) : GeneralLinear (t + 1) F) * g⁻¹⁻¹
    exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const
  let K : Subgroup H := K₁.toSubgroup.comap φ ⊓ (χ.comp (H : Subgroup N).subtype).ker
  have hKopen : IsOpen (K : Set H) := by
    rw [Subgroup.coe_inf, Subgroup.coe_comap, ← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact (K₁.isOpen.preimage hφ).inter
      ((isOpen_ker_inverseStandardCharacter F ψ t).preimage continuous_subtype_val)
  have : IsTopologicalGroup N := inferInstance
  have : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup (H : Subgroup N))
  have : Finite (H ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
  let := Fintype.ofFinite (H ⧸ K)
  refine ⟨H ⧸ K, inferInstance,
    fun c => (((Quotient.out c : H) : N) : GeneralLinear (t + 1) F) * g,
    fun c => (Fintype.card (H ⧸ K) : ℂ)⁻¹ * (χ ((Quotient.out c : H) : N) : ℂ)⁻¹,
    fun u y => ?_⟩
  have hfix : ∀ k' ∈ K, (χ (k' : N) : ℂ)⁻¹ •
      twoBlockDeformedInduced F m h σ u ((k' : N) : GeneralLinear (t + 1) F)
        (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) =
      twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀) := by
    intro k' hk'
    exact inv_smul_inducedRep_flatSection_of_mem F h σ u v₀ g (z := χ (k' : N)) hk'.2 hk'.1
  have havg := Jacquet.Localization.characterAverage_eq_quotient_sum
    (T.isSmooth_normalizedOppositeParabolicInduced (succBlockShape m h)
      ((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u)))
    (isOpen_ker_inverseStandardCharacter F ψ t) H (isCompact_unipotentExhaustion F (t + 1) k)
    (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) K hfix
  change sectionEval F h _ (Jacquet.Localization.characterAverage _ _ H _ _) y = _
  rw [havg, sectionEval_smul, sectionEval_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sectionEval_smul]
  change (Fintype.card (H ⧸ K) : ℂ)⁻¹ • ((χ ((Quotient.out c : H) : N) : ℂ)⁻¹ •
      flatFunction F h σ u v₀ (y * (((Quotient.out c : H) : N) : GeneralLinear (t + 1) F)
        * g)) = _
  unfold flatFunction
  rw [smul_smul, smul_smul, smul_smul, mul_assoc y]
  congr 1
  ring

end Average

section Main

/-- The deformed Whittaker coefficients of flat sections are entire. -/
theorem flatCoefficientDifferentiable : FlatCoefficientDifferentiable F h σ ψ := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (t + 1)
  intro _ ell _ μ _ J hJ htop v₀ g
  obtain ⟨E, hE, hEsub⟩ := exists_matrix_exhaustion F (m 0 + 1) (m 1 + 1)
  let Fu : ∀ u : ℂ, Sections F h (twoBlockDeformedBlocks F m σ u) := fun u =>
    twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)
  let P : ∀ u : ℂ, ℕ → Sections F h (twoBlockDeformedBlocks F m σ u) := fun u k =>
    deformedAverage F h σ ψ u k (Fu u)
  let X : ℕ → ℕ → Set ℂ := fun k R =>
    {u | ∀ x ∉ E R, radicalRestriction F h _ (P u k) x = 0}
  have hcover : ∀ u, ∃ k R, u ∈ X k R := by
    intro u
    obtain ⟨k, hk⟩ := exists_deformedAverage_mem F h σ ψ u (htop u) (Fu u)
    have hc : HasCompactSupport (radicalRestriction F h _ (P u k)) := hk
    obtain ⟨R, hR⟩ := hEsub _ hc.isCompact
    exact ⟨k, R, fun x hx => image_eq_zero_of_notMem_tsupport (fun hx' => hx (hR hx'))⟩
  have hunc : ∃ k R, ¬ (X k R).Countable := by
    by_contra hcon
    push Not at hcon
    apply not_countable_complex
    have huniv : (Set.univ : Set ℂ) = ⋃ k, ⋃ R, X k R := by
      ext u
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact hcover u
    rw [huniv]
    exact Set.countable_iUnion fun k => Set.countable_iUnion fun R => hcon k R
  obtain ⟨k, R, hXR⟩ := hunc
  obtain ⟨ι, _, d, a, hform⟩ := exists_deformedAverage_formula F h σ ψ v₀ g k
  let β : ι → Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℝ := fun i x =>
    blockZeroNorm F h (upperRadical h F x * d i)
  let w : ι → Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → PiTensorProduct ℂ W :=
    fun i x => a i • sectionEval F h _ v₀ (upperRadical h F x * d i)
  have hval : ∀ u x, radicalRestriction F h _ (P u k) x =
      ∑ i, ((β i x : ℂ) ^ u) • w i x :=
    fun u x => hform u (upperRadical h F x)
  have hall : ∀ u, ∀ x ∉ E R, radicalRestriction F h _ (P u k) x = 0 := by
    intro u x hx
    rw [hval]
    refine sum_cpow_smul_eq_zero_of_not_countable Finset.univ (fun i => β i x)
      (fun i => blockZeroNorm_pos F h _) (fun i => w i x)
      (fun hc => hXR (Set.Countable.mono (fun u' hu' => ?_) hc)) u
    rw [Set.mem_ofPred_eq, ← hval]
    exact hu' x hx
  have hmem : ∀ u, P u k ∈ compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) :=
    fun u => HasCompactSupport.intro (hE R) (hall u)
  let α : ι → Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun i x =>
    a i * tensorContraction ell (sectionEval F h _ v₀ (upperRadical h F x * d i)) *
      positiveKernel ψ x
  have hcont : ∀ i, Continuous fun x => upperRadical h F x * d i := fun i =>
    (continuous_upperRadical h F).mul continuous_const
  have hα : ∀ i, Continuous (α i) := fun i =>
    (continuous_const.mul ((((Induction.eval_isLocallyConstant _ _ v₀).comp
      (tensorContraction ell)).comp_continuous (hcont i)).continuous)).mul
      (continuous_positiveKernel ψ)
  have hβ : ∀ i, IsLocallyConstant (β i) := fun i =>
    (isLocallyConstant_blockZeroNorm F h).comp_continuous (hcont i)
  have hint : ∀ i (u : ℂ), IntegrableOn (fun x => α i x * (β i x : ℂ) ^ u) (E R) μ := by
    intro i u
    exact ContinuousOn.integrableOn_compact (hE R)
      ((hα i).mul ((hβ i).comp fun b : ℝ => (b : ℂ) ^ u).continuous).continuousOn
  have hJu : ∀ u, (J u).val (Fu u) = ∑ i, ∫ x in E R, α i x * (β i x : ℂ) ^ u ∂μ := by
    intro u
    rw [← functional_deformedAverage F h σ ψ u k (J u) (Fu u)]
    change (J u).val (P u k) = _
    rw [hJ u _ (hmem u), jacquetFunction_def]
    have hfun : integrand ψ ell (P u k) 1 = fun x =>
        tensorContraction ell (radicalRestriction F h _ (P u k) x) * positiveKernel ψ x := by
      funext x
      rw [integrand_def, scalarSection_one, mul_one]
      rfl
    rw [hfun, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := E R) (fun x hx => by
      rw [hall u x hx, map_zero, zero_mul]), ← integral_finsetSum Finset.univ
        (fun i _ => hint i u)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    change _ = ∑ i, α i x * (β i x : ℂ) ^ u
    rw [hval u x, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, α, map_smul, smul_eq_mul]
    ring
  have hfun : (fun u : ℂ => (J u).val
      (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀))) =
      fun u => ∑ i, ∫ x in E R, α i x * (β i x : ℂ) ^ u ∂μ := funext hJu
  rw [hfun]
  exact Differentiable.fun_sum fun i _ =>
    differentiable_setIntegral_mul_cpow μ (hE R) (hβ i) (fun x => blockZeroNorm_pos F h _)
      ((hα i).continuousOn.integrableOn_compact (hE R))

end Main

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
