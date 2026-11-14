import Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalytic
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationUniqueness
/-!
# Assembly of the entire deformation from the analytic input

For every complex `u`, the JPSS integral (4.6.2) at the identity on the compact-radical
sections of `ρ_u` extends to an inverse-character Whittaker functional `J_u` of `ρ_u`.
Together with the relations it spans `ρ_u`. Given the analytic input
`FlatCoefficientDifferentiable` and uniqueness of inverse-character functionals, the family
`W_u(g) = c · J_u(ρ_u(g) f_u)` of flat sections `f_u` satisfies the four clauses of
`TwoBlockWhittakerDeformationStatement`. The analytic input is
`flatCoefficientDifferentiable`, so the closed proposition follows from
`NormalizedProductWhittakerTypeStatement` alone.
-/

noncomputable section

open MeasureTheory Topology Filter

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding FlatCoefficientDifferentiable blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos character_eq_one_mem_nhds compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule deformedAverage deformedBlockFunctional deformedBlockFunctional_val determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_block_inverse_functional exists_deformation_of_differentiable exists_deformation_of_functionals exists_deformedAverage_formula exists_deformedAverage_mem exists_deformed_section_jacquetFunction_one_ne_zero exists_jacquetFunctional exists_matrix_exhaustion exists_mem_unipotentExhaustion exists_oppositeParabolic_mul exists_section_jacquetFunction_one_ne_zero exists_uniform_stabilizer exists_upperUnipotent_exhaustion flatCoefficientDifferentiable flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen functional_deformedAverage functional_eq_smul inducedRep_flatSection_of_mem inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inv_smul_inducedRep_flatSection_of_mem inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isCompact_unipotentExhaustion isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm isOfWhittakerType_twoBlockDeformedInduced isOpen_ker_inverseStandardCharacter isSmooth_twoBlockDeformedBlocks jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower monotone_unipotentExhaustion oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer sectionEval_sum tensorContraction_blockTensor twoBlockDeformedBlocks_isOfWhittakerType_iff twoBlockWhittakerDeformationStatement_of twoBlockWhittakerDeformationStatement_of_normalizedProduct unipotentExhaustion
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet

universe uF uW

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

section Extension

variable [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]

/-- The JPSS integral at the identity on the compact-radical sections extends to an
inverse-character Whittaker functional `J` of the actual lower induction. If some
compact-radical section has nonzero integral and the inverse-character functionals are
unique up to scalars, then `J ≠ 0` and the character relations together with the
compact-radical sections span the whole induced space. -/
theorem exists_jacquetFunctional [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (hell : ∀ i, ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure],
      (∃ f ∈ compactRadicalSubmodule F h σ, jacquetFunction ψ ell μ f 1 ≠ 0) →
      (∀ φ φ' : glInverseFunctionals ψ t (inducedRep F h σ),
        φ'.val ≠ 0 → ∃ c : ℂ, φ.val = c • φ'.val) →
      ∃ J : glInverseFunctionals ψ t (inducedRep F h σ),
        (∀ f ∈ compactRadicalSubmodule F h σ, J.val f = jacquetFunction ψ ell μ f 1) ∧
        J.val ≠ 0 ∧
        Jacquet.Localization.relations (inducedRep F h σ) (upperUnipotent (t + 1) F)
          (inverseStandardCharacter ψ t) ⊔ compactRadicalSubmodule F h σ = ⊤ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1)
  intro _ μ _ hne huniq
  have hρ : IsSmooth (inducedRep F h σ) :=
    T.isSmooth_normalizedOppositeParabolicInduced _ _
  have hχ := isOpen_ker_inverseStandardCharacter F ψ t
  obtain ⟨S, hS, hmono, hcover⟩ := exists_upperUnipotent_exhaustion F (t + 1)
  have hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1 :=
    fun f hf => isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule F h σ ψ ell μ hf
  let J' := compactRadicalJacquet F h σ ψ ell μ hint
  have hV' : ∀ (n : upperUnipotent (t + 1) F) (v : Sections F h σ),
      v ∈ compactRadicalSubmodule F h σ →
        inducedRep F h σ n v ∈ compactRadicalSubmodule F h σ :=
    fun n v hv => inducedRep_mem_compactRadicalSubmodule F h σ n hv
  have hJ' : ∀ (n : upperUnipotent (t + 1) F) (v : compactRadicalSubmodule F h σ),
      J' ⟨inducedRep F h σ n v, hV' n v v.property⟩ =
        (inverseStandardCharacter ψ t n : ℂ) * J' v :=
    fun n v => compactRadicalJacquet_inducedRep F h σ ψ ell hell μ hint n v
  obtain ⟨f₀, hf₀, hJf₀⟩ := hne
  have hJ'f₀ : J' ⟨f₀, hf₀⟩ ≠ 0 := hJf₀
  have hJ'0 : J' ≠ 0 := fun h0 => hJ'f₀ (by rw [h0, LinearMap.zero_apply])
  obtain ⟨J, hJ⟩ := Jacquet.Localization.exists_functional_extension
    (compactRadicalSubmodule F h σ) J'
    (fun v hv hr => Jacquet.Localization.apply_eq_zero_of_mem_relations hρ hχ S hS hmono
      hcover (compactRadicalSubmodule F h σ) hV' J' hJ' hv hr)
  refine ⟨J, fun f hf => hJ ⟨f, hf⟩, fun h0 => hJ'f₀ ?_, ?_⟩
  · rw [← hJ ⟨f₀, hf₀⟩, h0, LinearMap.zero_apply]
  · refine Jacquet.Localization.relations_sup_eq_top hρ hχ S hS hmono hcover
      (compactRadicalSubmodule F h σ) hV' J' hJ' (fun φ φ' hφ' => ?_) hJ'0
    obtain ⟨c, hc⟩ := huniq φ φ' hφ'
    exact ⟨c, Subtype.ext hc⟩

end Extension

/-- The four clauses from a family of nonzero inverse-character functionals `J_u` on `ρ_u`
whose flat coefficients `u ↦ J_u(ρ_u(g) f_u)` are entire, provided every inverse-character
functional on `ρ_0` is a multiple of `J_0`. The family is `W_u(g) = c · J_u(ρ_u(g) f_u)` with
`ℓ₀ = c · J_0` and `f_u` the flat section through `v₀`. -/
theorem exists_deformation_of_functionals [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (J : ∀ u : ℂ, glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u))
    (hJ0 : ∀ u, (J u).val ≠ 0)
    (huniq : ∀ ℓ : (glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0)),
      ∃ c : ℂ, ℓ.val = c • (J 0).val)
    (ℓ₀ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0) (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (hdiff : ∀ g : GeneralLinear (t + 1) F, Differentiable ℂ (fun u : ℂ =>
      (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)))) :
    ∃ Wu : ℂ → GeneralLinear (t + 1) F → ℂ,
      (∀ g, Wu 0 g = ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀)) ∧
      (∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockDeformedInduced F m h σ u g v)) ∧
      (∃ K : Subgroup (GeneralLinear (t + 1) F),
        IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K), Wu u (g * k) = Wu u g) ∧
      ∀ (g : GeneralLinear (t + 1) F) (u : ℂ), AnalyticAt ℂ (fun z => Wu z g) u := by
  obtain ⟨c, hc⟩ := huniq ℓ₀
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hℓ₀ (by rw [hc, zero_smul])
  obtain ⟨K, hKo, hKc, hK⟩ := exists_uniform_stabilizer F h σ v₀
  have c1 : ∀ g, c * (J 0).val (twoBlockDeformedInduced F m h σ 0 g (flatSection F h σ 0 v₀)) =
      ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀) := by
    intro g
    have e : twoBlockDeformedInduced F m h σ 0 g (flatSection F h σ 0 v₀) =
        twoBlockDeformedInduced F m h σ 0 g v₀ :=
      congrArg (twoBlockDeformedInduced F m h σ 0 g) (flatSection_zero F h σ v₀)
    have e2 : ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀) =
        (c • (J 0).val) (twoBlockDeformedInduced F m h σ 0 g v₀) :=
      LinearMap.congr_fun hc _
    exact (congrArg (fun v => c * (J 0).val v) e).trans e2.symm
  have c2 : ∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
      ℓ.val ≠ 0 ∧ ∃ v, ∀ g,
        c * (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) =
          ℓ.val (twoBlockDeformedInduced F m h σ u g v) := by
    intro u
    refine ⟨c • J u, ?_, flatSection F h σ u v₀, fun g => ?_⟩
    · exact (Submodule.coe_smul c (J u)).symm ▸ smul_ne_zero hc0 (hJ0 u)
    · exact (smul_eq_mul c _).symm.trans (LinearMap.smul_apply c (J u).val _).symm
  have c3 : ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K),
      c * (J u).val (twoBlockDeformedInduced F m h σ u (g * k) (flatSection F h σ u v₀)) =
        c * (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) := by
    intro u g k
    have hm := LinearMap.congr_fun ((twoBlockDeformedInduced F m h σ u).map_mul g k)
      (flatSection F h σ u v₀)
    have e : twoBlockDeformedInduced F m h σ u (g * k) (flatSection F h σ u v₀) =
        twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀) :=
      hm.trans (congrArg (twoBlockDeformedInduced F m h σ u g) (hK u k))
    exact congrArg (fun v => c * (J u).val v) e
  have c4 : ∀ (g : GeneralLinear (t + 1) F) (u : ℂ), AnalyticAt ℂ (fun z =>
      c * (J z).val (twoBlockDeformedInduced F m h σ z g (flatSection F h σ z v₀))) u :=
    fun g u => ((hdiff g).const_mul c).analyticAt u
  exact ⟨fun u g => c * (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)),
    c1, c2, ⟨K, hKo, hKc, c3⟩, c4⟩

/-- JPSS (1983), Section (4.5), assembled from the analytic input: conditional on
`NormalizedProductWhittakerTypeStatement` (uniqueness of inverse-character functionals on
every `ρ_u`) and on `FlatCoefficientDifferentiable` (entire dependence of the flat
coefficients), every coefficient `g ↦ ℓ₀(ρ₀(g) v₀)` of a nonzero inverse-character
functional of `ρ₀` lies in an entire family with all four clauses of
`TwoBlockWhittakerDeformationStatement`. -/
theorem exists_deformation_of_differentiable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hA : FlatCoefficientDifferentiable F h σ ψ)
    (ℓ₀ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0) (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    ∃ Wu : ℂ → GeneralLinear (t + 1) F → ℂ,
      (∀ g, Wu 0 g = ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀)) ∧
      (∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockDeformedInduced F m h σ u g v)) ∧
      (∃ K : Subgroup (GeneralLinear (t + 1) F),
        IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K), Wu u (g * k) = Wu u g) ∧
      ∀ (g : GeneralLinear (t + 1) F) (u : ℂ), AnalyticAt ℂ (fun z => Wu z g) u := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  have : BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (BorelSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
      μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  choose l hl0 using exists_block_inverse_functional F m ψ σ hσ
  let ell : ∀ i, W i →ₗ[ℂ] ℂ := fun i => (l i).val
  have hex : ∀ u : ℂ, ∃ J : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
      (∀ f ∈ compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u),
        J.val f = jacquetFunction ψ ell μ f 1) ∧
      J.val ≠ 0 ∧
      Jacquet.Localization.relations (twoBlockDeformedInduced F m h σ u)
          (upperUnipotent (t + 1) F) (inverseStandardCharacter ψ t) ⊔
        compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u) = ⊤ := by
    intro u
    obtain ⟨f, hf, hJf⟩ :=
      exists_deformed_section_jacquetFunction_one_ne_zero F h ψ σ hσ ell hl0 u μ
    exact exists_jacquetFunctional F h ψ (twoBlockDeformedBlocks F m σ u) ell
      (fun i => (deformedBlockFunctional F m ψ σ u i (l i)).property) μ ⟨f, hf, hJf⟩
      (fun φ φ' hφ' => functional_eq_smul F m h H ψ σ hσ u φ' φ hφ')
  choose J hJ hJ0 htop using hex
  exact exists_deformation_of_functionals F h ψ σ J hJ0
    (fun ℓ => functional_eq_smul F m h H ψ σ hσ 0 (J 0) ℓ (hJ0 0)) ℓ₀ hℓ₀ v₀
    (hA ell μ J hJ htop v₀)

/-- The closed target `TwoBlockWhittakerDeformationStatement`, conditional on
`NormalizedProductWhittakerTypeStatement` and on `FlatCoefficientDifferentiable` for all
blocks of full standard Whittaker type. -/
theorem twoBlockWhittakerDeformationStatement_of
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (hA : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
      ∀ (ψ : UnitaryAdditiveCharacter F) (t : ℕ) (m : Fin 2 → ℕ)
        (h : ∑ i, (m i + 1) = t + 1)
        {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
        (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
        (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
          FlatCoefficientDifferentiable F h σ ψ) :
    TwoBlockWhittakerDeformationStatement.{uF, uW} := by
  intro F _ _ _ _ ψ t m h W _ _ σ hσ ℓ₀ hℓ₀ v₀
  exact exists_deformation_of_differentiable F h H ψ σ hσ (hA F ψ t m h σ hσ) ℓ₀ hℓ₀ v₀

/-- The closed deformation proposition, conditional only on the full Whittaker type of the
upper normalized products: the analytic input is `flatCoefficientDifferentiable`. -/
theorem twoBlockWhittakerDeformationStatement_of_normalizedProduct
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW}) :
    TwoBlockWhittakerDeformationStatement.{uF, uW} :=
  twoBlockWhittakerDeformationStatement_of H
    fun F _ _ _ _ ψ _ _ h _ _ _ σ _ => flatCoefficientDifferentiable F h σ ψ

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
