import Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance
import Langlands.Representation.Whittaker.SubgroupFunctionalExtension
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof

/-! # The absolute-domain lower Jacquet functional of the rank-one extension -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis MeasureTheory
open scoped Matrix NNReal

universe uF uW

section Algebra

variable {K : Type uF} [Field K] {t : ℕ}

/-- The row substitution `y ↦ α⁻¹ (y + β)` attached to `n = u(β) B(α, 0, 1)`. -/
def rankOneExtensionUnipotentShift (n : upperUnipotent (1 + (t + 1)) K)
    (y : Fin (t + 1) → K) : Fin (t + 1) → K :=
  ((rankOneExtensionUnipotentHead n)⁻¹).val *ᵥ (y + rankOneExtensionUnipotentColumn n)

/-- The cell factorization `u(y) n = B(α, 0, 1) u(α⁻¹ (y + β))`. -/
theorem rankOneExtensionUpperCell_mul_unipotent (n : upperUnipotent (1 + (t + 1)) K)
    (y : Fin (t + 1) → K) :
    rankOneExtensionUpperCell t y * n.val =
      rankOneExtensionLowerBlock t (rankOneExtensionUnipotentHead n) 0 1 *
        rankOneExtensionUpperCell t (rankOneExtensionUnipotentShift n y) := by
  rw [rankOneExtensionLowerBlock_upperCell, rankOneExtensionUnipotentShift,
    Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_lhs => rw [rankOneExtensionUnipotent_decomposition n]
  rw [← mul_assoc, rankOneExtensionUpperCell_mul]

/-- An upper unipotent matrix fixes the last coordinate of a column. -/
theorem upperUnipotent_mulVec_last {d : ℕ} (u : Langlands.GeneralLinear (d + 1) K)
    (hu : u ∈ upperUnipotent (d + 1) K) (v : Fin (d + 1) → K) :
    (u.val *ᵥ v) (Fin.last d) = v (Fin.last d) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have h (i : Fin d) : u.val (Fin.last d) i.castSucc = 0 :=
    hu.1 (Fin.castSucc_lt_last i)
  simp [h, hu.2 (Fin.last d)]

theorem rankOneExtensionUnipotentShift_last (n : upperUnipotent (1 + (t + 1)) K)
    (y : Fin (t + 1) → K) :
    rankOneExtensionUnipotentShift n y (Fin.last t) =
      y (Fin.last t) + rankOneExtensionUnipotentColumn n (Fin.last t) := by
  rw [rankOneExtensionUnipotentShift,
    upperUnipotent_mulVec_last _ (inv_mem (rankOneExtensionUnipotentHead_mem n))]
  rfl

/-- The first-superdiagonal sum of `n = [α, β; 0, 1]` splits as that of `α` plus the
last entry of `β`. -/
theorem rankOneExtension_superdiagonal_sum (n : upperUnipotent (1 + (t + 1)) K) :
    ∑ i : Fin (1 + t), n.val.val i.castSucc i.succ =
      ∑ i : Fin t, (rankOneExtensionUnipotentHead n).val i.castSucc i.succ +
        rankOneExtensionUnipotentColumn n (Fin.last t) := by
  let e : ℕ → K := fun k =>
    if h : k + 1 < 1 + (t + 1) then n.val.val ⟨k, by omega⟩ ⟨k + 1, h⟩ else 0
  have h1 : ∑ i : Fin (1 + t), n.val.val i.castSucc i.succ =
      ∑ k ∈ Finset.range (1 + t), e k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) + 1 < 1 + (t + 1) := by omega
    simp only [e, hi, ↓reduceDIte]
    rfl
  have h2 : ∑ i : Fin t, (rankOneExtensionUnipotentHead n).val i.castSucc i.succ =
      ∑ k ∈ Finset.range t, e k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) + 1 < 1 + (t + 1) := by omega
    simp only [e, hi, ↓reduceDIte]
    change rankOneExtensionCellBlocks t n.val (Sum.inl i.castSucc) (Sum.inl i.succ) = _
    rw [rankOneExtensionCellBlocks_apply]
    congr 1
  have h3 : rankOneExtensionUnipotentColumn n (Fin.last t) = e t := by
    have ht : t + 1 < 1 + (t + 1) := by omega
    simp only [e, ht, ↓reduceDIte]
    change rankOneExtensionCellBlocks t n.val (Sum.inl (Fin.last t)) (Sum.inr 0) = _
    rw [rankOneExtensionCellBlocks_apply]
    congr 1
  rw [h1, h2, h3, add_comm 1 t, Finset.sum_range_succ]

/-- The inverse standard character splits as `θ(n) = θ_t(α) ψ(β_last)⁻¹`. -/
theorem rankOneExtension_inverseStandardCharacter [TopologicalSpace K]
    (ψ : UnitaryAdditiveCharacter K) (n : upperUnipotent (1 + (t + 1)) K) :
    (Whittaker.inverseStandardCharacter ψ (1 + t) n : ℂ) =
      (Whittaker.inverseStandardCharacter ψ t
          ⟨rankOneExtensionUnipotentHead n, rankOneExtensionUnipotentHead_mem n⟩ : ℂ) *
        (ψ.complex (rankOneExtensionUnipotentColumn n (Fin.last t)))⁻¹ := by
  rw [Whittaker.inverseStandardCharacter_apply, Whittaker.inverseStandardCharacter_apply,
    rankOneExtension_superdiagonal_sum, AddChar.map_add_eq_mul, mul_inv]

end Algebra

section Measure

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] {t : ℕ}

/-- The transpose of `α⁻¹`, so that `α⁻¹ *ᵥ x = x ᵥ* (α⁻¹)ᵀ`. -/
def rankOneExtensionShiftMatrix (n : upperUnipotent (1 + (t + 1)) K) :
    Langlands.GeneralLinear (t + 1) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((rankOneExtensionUnipotentHead n)⁻¹).valᵀ (by
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (rankOneExtensionUnipotentHead n)⁻¹.isUnit).ne_zero)

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] in
theorem det_rankOneExtensionShiftMatrix (n : upperUnipotent (1 + (t + 1)) K) :
    Matrix.det (rankOneExtensionShiftMatrix n).val = 1 := by
  change Matrix.det ((rankOneExtensionUnipotentHead n)⁻¹).valᵀ = 1
  rw [Matrix.det_transpose]
  exact unipotent_det ⟨_, inv_mem (rankOneExtensionUnipotentHead_mem n)⟩

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
theorem rankOneExtensionUnipotentShift_eq (n : upperUnipotent (1 + (t + 1)) K) :
    rankOneExtensionUnipotentShift n =
      rowHomeomorph (rankOneExtensionShiftMatrix n) ∘
        (Homeomorph.addRight (rankOneExtensionUnipotentColumn n)) := by
  funext y
  change _ = (y + rankOneExtensionUnipotentColumn n) ᵥ*
    ((rankOneExtensionUnipotentHead n)⁻¹).valᵀ
  rw [Matrix.vecMul_transpose]
  rfl

theorem measurableEmbedding_rankOneExtensionUnipotentShift
    (n : upperUnipotent (1 + (t + 1)) K) :
    MeasurableEmbedding (rankOneExtensionUnipotentShift n) := by
  rw [rankOneExtensionUnipotentShift_eq]
  exact (rowHomeomorph _).measurableEmbedding.comp (Homeomorph.addRight _).measurableEmbedding

/-- The substitution `y ↦ α⁻¹ (y + β)` preserves the row product of every Haar measure
with a scalar change-of-variables character. -/
theorem measurePreserving_rankOneExtensionUnipotentShift (χ : K →*₀ ℝ≥0)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]
    (hχ : ∀ a : K, a ≠ 0 → ν.measure.map (fun x => a * x) = (χ a)⁻¹ • ν.measure)
    (n : upperUnipotent (1 + (t + 1)) K) :
    MeasurePreserving (rankOneExtensionUnipotentShift n) (rowMeasure ν (t + 1))
      (rowMeasure ν (t + 1)) := by
  rw [rankOneExtensionUnipotentShift_eq]
  refine MeasurePreserving.comp ⟨(rowHomeomorph _).continuous.measurable, ?_⟩
    (measurePreserving_add_right _ _)
  change (rowMeasure ν (t + 1)).map (fun x => x ᵥ* (rankOneExtensionShiftMatrix n).val) = _
  rw [rowMeasure_map_vecMul χ ν hχ, det_rankOneExtensionShiftMatrix, map_one, inv_one, one_smul]

end Measure

section Covariance

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {t : ℕ}

local instance : ∀ i : Fin 2,
    AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instAddCommGroup i.rev

local instance : ∀ i : Fin 2,
    Module ℂ (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instModule ℂ i.rev

/-- Contracting with `ℓ ∘ σ(u)` multiplies the contraction with `ℓ` by `θ_t(u)`. -/
theorem rankOneExtensionTensorContraction_comp_unipotent
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (u : upperUnipotent (t + 1) F.Carrier) (T : rankOneExtensionLowerTensor (W := W)) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ u.val) T =
      (Whittaker.inverseStandardCharacter ψ t u : ℂ) *
        rankOneExtensionTensorContraction ℓ.val T := by
  let := F.canonicalTopologicalData.topology
  refine piTensorProduct_comp_apply_eq_mul LinearMap.id _ _ _ (fun v => ?_) T
  rw [LinearMap.id_apply]
  erw [rankOneExtensionTensorContraction_tprod, rankOneExtensionTensorContraction_tprod]
  change ℓ.val (σ u.val (v 0)) * _ = _ * (ℓ.val (v 0) * _)
  rw [ℓ.property u (v 0), mul_assoc]

/-- The lower block `B(u, 0, 1)` with `u` upper unipotent multiplies the scalar coefficient
by `θ_t(u)`. -/
theorem rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul
    {χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (u : upperUnipotent (t + 1) F.Carrier)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t u.val 0 1 * g) =
      (Whittaker.inverseStandardCharacter ψ t u : ℂ) *
        rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f g := by
  let := F.canonicalTopologicalData.topology
  have hdet : F.canonicalTopologicalData.determinantNorm (t + 1) u.val = 1 := by
    change F.canonicalTopologicalData.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [show GeneralLinear.determinant u.val = 1 from Units.ext (unipotent_det u), map_one]
  rw [rankOneExtensionLowerSectionCoefficient_lowerBlock_mul, hdet, map_one, one_pow, div_one,
    map_one, Units.val_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, one_mul, one_mul]
  exact rankOneExtensionTensorContraction_comp_unipotent ℓ u _

/-- Left translation of the ambient element by `n ∈ N` multiplies the integrand by
`θ(n)` and substitutes `y ↦ α⁻¹ (y + β)`. -/
theorem rankOneExtensionStableIntegrand_unipotent_mul
    {χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (n : upperUnipotent (1 + (t + 1)) F.Carrier)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) (y : Fin (t + 1) → F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ f (n.val * g) y =
      (Whittaker.inverseStandardCharacter ψ (1 + t) n : ℂ) *
        rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g (rankOneExtensionUnipotentShift n y) := by
  let := F.canonicalTopologicalData.topology
  have hψ (b : F.Carrier) : ψ.complex b ≠ 0 := by
    intro h
    have h' := AddChar.map_add_eq_mul ψ.complex b (-b)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h'
    exact one_ne_zero h'
  rw [rankOneExtensionStableIntegrand_apply, rankOneExtensionStableIntegrand_apply, ← mul_assoc,
    rankOneExtensionUpperCell_mul_unipotent, mul_assoc,
    rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul ℓ f
      ⟨_, rankOneExtensionUnipotentHead_mem n⟩,
    rankOneExtension_inverseStandardCharacter, rankOneExtensionUnipotentShift_last,
    AddChar.map_add_eq_mul]
  have hβ := hψ (rankOneExtensionUnipotentColumn n (Fin.last t))
  field_simp

end Covariance

section Extension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {X : Type*} [MeasurableSpace X]

/-- An integral functional whose integrand transforms under `U` by `θ` and a
measure-preserving substitution is `θ`-equivariant on the subspace where it converges
absolutely, and smooth localization exactness extends it to the whole space. -/
theorem exists_functional_eq_integral_of_covariant (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ : Representation ℂ G V) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ))) (hρ : IsSmooth ρ)
    (Φ : V →ₗ[ℂ] X → ℂ) (μ : Measure X) (s : U → X → X)
    (hs : ∀ n, MeasurePreserving (s n) μ μ) (hse : ∀ n, MeasurableEmbedding (s n))
    (hΦ : ∀ (n : U) (v : V), Φ (ρ n v) = fun y => (θ n : ℂ) * Φ v (s n y)) :
    ∃ L : Whittaker.functionals U θ ρ,
      ∀ v, Integrable (Φ v) μ → L.val v = ∫ y, Φ v y ∂μ := by
  let D : Submodule ℂ V :=
    { carrier := {v | Integrable (Φ v) μ}
      zero_mem' := by
        change Integrable (Φ 0) μ
        rw [map_zero]
        exact integrable_zero _ _ _
      add_mem' := fun {v w} hv hw => by
        change Integrable (Φ (v + w)) μ
        rw [map_add]
        exact hv.add hw
      smul_mem' := fun c v hv => by
        change Integrable (Φ (c • v)) μ
        rw [map_smul]
        exact hv.smul c }
  have hD (n : U) (v : V) (hv : v ∈ D) : ρ n v ∈ D := by
    change Integrable (Φ (ρ n v)) μ
    rw [hΦ]
    exact (((hs n).integrable_comp_emb (hse n)).mpr hv).const_mul _
  let τ : Representation ℂ U D :=
    Representation.subrepresentation (ρ.comp U.subtype) D (fun n v hv => hD n v hv)
  let i : τ.IntertwiningMap (ρ.comp U.subtype) :=
    { toLinearMap := D.subtype
      isIntertwining' := fun _ => rfl }
  let J : D →ₗ[ℂ] ℂ :=
    { toFun v := ∫ y, Φ v.val y ∂μ
      map_add' v w := by
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
        exact integral_add v.property w.property
      map_smul' c v := by
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hJ : J ∈ Whittaker.functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ := by
    intro n v
    change ∫ y, Φ (ρ n.val v.val) y ∂μ = (θ n.val : ℂ) * ∫ y, Φ v.val y ∂μ
    rw [hΦ, integral_const_mul, (hs n.val).integral_comp (hse n.val)]
  obtain ⟨L, hL⟩ := Whittaker.exists_functional_extension_of_subgroup_intertwiner
    U θ ρ τ hU hθ i Subtype.val_injective hρ ⟨J, hJ⟩
  exact ⟨L, fun v hv => hL ⟨v, hv⟩⟩


end Extension

/-- The absolute-domain lower Jacquet functional: the integral functional on the subspace
where the integrand at the identity is integrable, extended to the whole lower induction. -/
theorem rankOneExtensionLowerJacquetFunctional :
    RankOneExtensionLowerJacquetFunctionalStatement.{uF, uW} := by
  intro p _ F W _ _ t χ σ ψ ℓ ν
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (1 + t + 1)
  let := T.upperUnipotentNonarchimedean (1 + t + 1)
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      ν.val.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.val.measure :=
    padicScalarHaarScaling F T ν.val.measure (Units.mk0 a ha)
  let I := rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ 1
  have hI (h : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier)
      (f : rankOneExtensionLowerSection F t χ σ) :
      I (rankOneExtensionLowerTranslate F t χ σ h f) =
        rankOneExtensionStableIntegrand F t χ σ ψ ℓ f h :=
    (rankOneExtensionStableIntegrand_translate F t χ σ ψ ℓ h 1 f).trans (by rw [one_mul])
  obtain ⟨L, hL⟩ := exists_functional_eq_integral_of_covariant _ _ _
    (upperUnipotent_isLimitOfCompactSubgroups F T (1 + t + 1))
    (isLocallyConstant_of_continuous_complex_character _
      (Whittaker.inverseStandardCharacterContinuous ψ (1 + t)).continuous)
    (T.isSmooth_normalizedOppositeParabolicInduced _ _)
    I (rowMeasure ν.val (t + 1)) rankOneExtensionUnipotentShift
    (measurePreserving_rankOneExtensionUnipotentShift T.normalizedAbsHom ν.val hχ)
    measurableEmbedding_rankOneExtensionUnipotentShift
    (fun n f => by
      funext y
      have h := rankOneExtensionStableIntegrand_unipotent_mul ℓ f n 1 y
      rw [mul_one] at h
      exact (congrFun (hI n.val f) y).trans h)
  refine ⟨L, fun f g hfg => ?_⟩
  have h := hL (rankOneExtensionLowerTranslate F t χ σ g f)
    ((congrArg (fun φ => Integrable φ (rowMeasure ν.val (t + 1))) (hI g f)).mpr hfg)
  refine h.trans ?_
  exact congrArg (fun φ => ∫ y, φ y ∂rowMeasure ν.val (t + 1)) (hI g f)

end Langlands.RankinSelberg
