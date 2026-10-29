import Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic
import Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness
import Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing

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

namespace Langlands.RankinSelberg.TwoBlockDeformation

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

section Extension

variable [MeasurableSpace F.Carrier] [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]

/-- The JPSS integral at the identity on the compact-radical sections extends to an
inverse-character Whittaker functional `J` of the actual lower induction. If some
compact-radical section has nonzero integral and the inverse-character functionals are
unique up to scalars, then `J ≠ 0` and the character relations together with the
compact-radical sections span the whole induced space. -/
theorem exists_jacquetFunctional
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (hell : ∀ i, letI := F.canonicalTopologicalData.topology
      ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure],
      (∃ f ∈ compactRadicalSubmodule F h σ, jacquetFunction ψ ell μ f 1 ≠ 0) →
      (∀ φ φ' : glInverseFunctionals ψ t (inducedRep F h σ),
        φ'.val ≠ 0 → ∃ c : ℂ, φ.val = c • φ'.val) →
      ∃ J : glInverseFunctionals ψ t (inducedRep F h σ),
        (∀ f ∈ compactRadicalSubmodule F h σ, J.val f = jacquetFunction ψ ell μ f 1) ∧
        J.val ≠ 0 ∧
        Jacquet.Localization.relations (inducedRep F h σ) (upperUnipotent (t + 1) F.Carrier)
          (inverseStandardCharacter ψ t) ⊔ compactRadicalSubmodule F h σ = ⊤ := by
  let T := F.canonicalTopologicalData
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
  have hV' : ∀ (n : upperUnipotent (t + 1) F.Carrier) (v : Sections F h σ),
      v ∈ compactRadicalSubmodule F h σ →
        inducedRep F h σ n v ∈ compactRadicalSubmodule F h σ :=
    fun n v hv => inducedRep_mem_compactRadicalSubmodule F h σ n hv
  have hJ' : ∀ (n : upperUnipotent (t + 1) F.Carrier) (v : compactRadicalSubmodule F h σ),
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
theorem exists_deformation_of_functionals
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (J : ∀ u : ℂ, letI := F.canonicalTopologicalData.topology
      glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u))
    (hJ0 : ∀ u, (J u).val ≠ 0)
    (huniq : ∀ ℓ : (letI := F.canonicalTopologicalData.topology
      glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0)),
      ∃ c : ℂ, ℓ.val = c • (J 0).val)
    (ℓ₀ : letI := F.canonicalTopologicalData.topology
      glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0) (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (hdiff : ∀ g : GeneralLinear (t + 1) F.Carrier, Differentiable ℂ (fun u : ℂ =>
      (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)))) :
    letI := F.canonicalTopologicalData.topology
    ∃ Wu : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ,
      (∀ g, Wu 0 g = ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀)) ∧
      (∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockDeformedInduced F m h σ u g v)) ∧
      (∃ K : Subgroup (GeneralLinear (t + 1) F.Carrier),
        IsOpen (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F.Carrier) (k : K), Wu u (g * k) = Wu u g) ∧
      ∀ (g : GeneralLinear (t + 1) F.Carrier) (u : ℂ), AnalyticAt ℂ (fun z => Wu z g) u := by
  let := F.canonicalTopologicalData.topology
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
  have c3 : ∀ (u : ℂ) (g : GeneralLinear (t + 1) F.Carrier) (k : K),
      c * (J u).val (twoBlockDeformedInduced F m h σ u (g * k) (flatSection F h σ u v₀)) =
        c * (J u).val (twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀)) := by
    intro u g k
    have hm := LinearMap.congr_fun ((twoBlockDeformedInduced F m h σ u).map_mul g k)
      (flatSection F h σ u v₀)
    have e : twoBlockDeformedInduced F m h σ u (g * k) (flatSection F h σ u v₀) =
        twoBlockDeformedInduced F m h σ u g (flatSection F h σ u v₀) :=
      hm.trans (congrArg (twoBlockDeformedInduced F m h σ u g) (hK u k))
    exact congrArg (fun v => c * (J u).val v) e
  have c4 : ∀ (g : GeneralLinear (t + 1) F.Carrier) (u : ℂ), AnalyticAt ℂ (fun z =>
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
theorem exists_deformation_of_differentiable
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hA : FlatCoefficientDifferentiable F h σ ψ)
    (ℓ₀ : letI := F.canonicalTopologicalData.topology
      glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0) (v₀ : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    letI := F.canonicalTopologicalData.topology
    ∃ Wu : ℂ → GeneralLinear (t + 1) F.Carrier → ℂ,
      (∀ g, Wu 0 g = ℓ₀.val (twoBlockDeformedInduced F m h σ 0 g v₀)) ∧
      (∀ u : ℂ, ∃ ℓ : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, Wu u g = ℓ.val (twoBlockDeformedInduced F m h σ u g v)) ∧
      (∃ K : Subgroup (GeneralLinear (t + 1) F.Carrier),
        IsOpen (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F.Carrier) (k : K), Wu u (g * k) = Wu u g) ∧
      ∀ (g : GeneralLinear (t + 1) F.Carrier) (u : ℂ), AnalyticAt ℂ (fun z => Wu z g) u := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  have : BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (BorelSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier),
      μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  choose l hl0 using exists_block_inverse_functional F m ψ σ hσ
  let ell : ∀ i, W i →ₗ[ℂ] ℂ := fun i => (l i).val
  have hex : ∀ u : ℂ, ∃ J : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u),
      (∀ f ∈ compactRadicalSubmodule F h (twoBlockDeformedBlocks F m σ u),
        J.val f = jacquetFunction ψ ell μ f 1) ∧
      J.val ≠ 0 ∧
      Jacquet.Localization.relations (twoBlockDeformedInduced F m h σ u)
          (upperUnipotent (t + 1) F.Carrier) (inverseStandardCharacter ψ t) ⊔
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
    (hA : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      letI := F.canonicalTopologicalData.topology
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (t : ℕ) (m : Fin 2 → ℕ)
        (h : ∑ i, (m i + 1) = t + 1)
        {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
        (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
        (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) →
          FlatCoefficientDifferentiable F h σ ψ) :
    TwoBlockWhittakerDeformationStatement.{uF, uW} := by
  intro p _ F ψ t m h W _ _ σ hσ ℓ₀ hℓ₀ v₀
  exact exists_deformation_of_differentiable F h H ψ σ hσ (hA p F ψ t m h σ hσ) ℓ₀ hℓ₀ v₀

/-- The closed deformation proposition, conditional only on the full Whittaker type of the
upper normalized products: the analytic input is `flatCoefficientDifferentiable`. -/
theorem twoBlockWhittakerDeformationStatement_of_normalizedProduct
    (H : NormalizedProductWhittakerTypeStatement.{uF, uW}) :
    TwoBlockWhittakerDeformationStatement.{uF, uW} :=
  twoBlockWhittakerDeformationStatement_of H
    fun _ _ F ψ _ _ h _ _ _ σ _ => flatCoefficientDifferentiable F h σ ψ

end Langlands.RankinSelberg.TwoBlockDeformation
