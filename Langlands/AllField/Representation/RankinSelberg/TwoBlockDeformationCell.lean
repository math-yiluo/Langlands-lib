import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
/-!
# The upper radical of the lower two-block induction

For the lower two-block induction `I(σ_1 ⊗ σ_2)` of `GL_(t+1)` with blocks of sizes
`m 0 + 1` and `m 1 + 1`, and the complementary upper radical `u(x) = [[1, x], [0, 1]]`,
this module proves the block factorization `u(x) n = diag(n_0, n_1) u(n_0⁻¹ (β + x n_1))`
of an upper unipotent matrix `n` with diagonal blocks `n_0, n_1` and upper-right block
`β`, the corresponding decomposition of the first-superdiagonal sum, and the
consequences for sections: the subspace of sections whose restriction to the upper
radical has compact support is stable under the upper unipotent group, and the
scalar integral `f ↦ ∫ ⟨f(u(x)), ⊗ λ_i⟩ ψ(x_(m 0, 0)) dx` is `ψ⁻¹`-equivariant for
block functionals `λ_i` equivariant for the inverse standard characters.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW uR

section Matrix

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {R : Type uR} [CommRing R]

section BlockSums


end BlockSums

end Matrix

section Sections

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- An upper unipotent matrix has determinant norm one. -/
theorem determinantNorm_eq_one_of_mem_upperUnipotent (T : LocalFieldData F) {n : ℕ}
    {g : GeneralLinear n F} (hg : g ∈ upperUnipotent n F) :
    T.determinantNorm n g = 1 := by
  have hdet : GeneralLinear.determinant g = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i])
  change T.normalizedAbsUnits (GeneralLinear.determinant g) = 1
  rw [hdet, map_one]

/-- The block modulus is trivial on Levi elements whose blocks have determinant norm one. -/
theorem leviModulus_eq_one (T : LocalFieldData F) (L : (succBlockShape m h).Levi F)
    (hL : ∀ i, T.determinantNorm (m i + 1) (L i) = 1) :
    T.leviModulus (succBlockShape m h) L = 1 := by
  rw [T.leviModulus_apply]
  exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
    change T.determinantNorm (m i + 1) (L i) ^ (m j + 1) /
      T.determinantNorm (m j + 1) (L j) ^ (m i + 1) = 1
    rw [hL i, hL j, one_pow, one_pow, div_one]

/-- Left translation by a Levi element with determinant-norm-one blocks acts on values by
the block tensor representation. -/
theorem sectionEval_leviEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h σ)
    (L : (succBlockShape m h).Levi F)
    (hL : ∀ i, (⟨⟩ : LocalFieldData F).determinantNorm (m i + 1) (L i) = 1)
    (g : GeneralLinear (t + 1) F) :
    sectionEval F h σ f ((succBlockShape m h).leviEmbedding F L * g) =
      (succBlockShape m h).blockTensor σ L (sectionEval F h σ f g) := by
  have hcov := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced_covariant
    (succBlockShape m h) ((succBlockShape m h).blockTensor σ) f
    ((succBlockShape m h).oppositeLeviInParabolic F L) g
  rw [BlockShape.oppositeLeviInParabolic_val, BlockShape.oppositeLeviProjection_section,
    leviModulus_eq_one F h _ L hL] at hcov
  rw [sectionEval, hcov]
  simp

/-- The restriction `x ↦ f(u(x))` of a section to the upper radical. -/
def radicalRestriction [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h σ) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    PiTensorProduct ℂ W :=
  sectionEval F h σ f (upperRadical h F x)

/-- An upper unipotent translate restricts through the block factorization. -/
theorem radicalRestriction_inducedRep [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : upperUnipotent (t + 1) F)
    (f : Sections F h σ) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    radicalRestriction F h σ (inducedRep F h σ n f) x =
      (succBlockShape m h).blockTensor σ (unipotentLevi h n)
        (radicalRestriction F h σ f (unipotentShift h n x)) := by
  change sectionEval F h σ f (upperRadical h F x * n.val) = _
  rw [upperRadical_mul_upperUnipotent, sectionEval_leviEmbedding_mul]
  · rfl
  · exact fun i => determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n i)

/-- The sections whose restriction to the upper radical has compact support. -/
def compactRadicalSubmodule [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Submodule ℂ (Sections F h σ) where
  carrier := {f | HasCompactSupport (radicalRestriction F h σ f)}
  zero_mem' := by
    change HasCompactSupport (fun x => sectionEval F h σ 0 (upperRadical h F x))
    simp only [sectionEval_zero]
    exact HasCompactSupport.zero
  add_mem' := by
    intro f f' hf hf'
    exact HasCompactSupport.add hf hf'
  smul_mem' := by
    intro c f hf
    exact hf.mono (Function.support_const_smul_subset c _)

theorem mem_compactRadicalSubmodule [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h σ) :
    f ∈ compactRadicalSubmodule F h σ ↔
      HasCompactSupport (radicalRestriction F h σ f) :=
  Iff.rfl

/-- The compact-radical sections are stable under the upper unipotent group. -/
theorem inducedRep_mem_compactRadicalSubmodule [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : upperUnipotent (t + 1) F)
    {f : Sections F h σ} (hf : f ∈ compactRadicalSubmodule F h σ) :
    inducedRep F h σ n f ∈ compactRadicalSubmodule F h σ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let φ := affineHomeomorph F (unipotentLevi h n 0) (unipotentCorner h n)
    (unipotentLevi h n 1)
  have hfun : radicalRestriction F h σ (inducedRep F h σ n f) =
      (succBlockShape m h).blockTensor σ (unipotentLevi h n) ∘
        (radicalRestriction F h σ f ∘ φ) := by
    funext x
    exact radicalRestriction_inducedRep F h σ n f x
  rw [mem_compactRadicalSubmodule, hfun]
  exact (HasCompactSupport.comp_homeomorph hf φ).comp_left (map_zero _)

section Contraction

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)

/-- Block functionals equivariant for the inverse standard characters scale the
contraction of a unipotent block translate by the product of the block characters. -/
theorem tensorContraction_blockTensor (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (hell : ∀ i, ell i ∈ glInverseFunctionals ψ (m i) (σ i))
    (L : (succBlockShape m h).Levi F) (hL : ∀ i, L i ∈ upperUnipotent (m i + 1) F)
    (v : PiTensorProduct ℂ W) :
    tensorContraction ell ((succBlockShape m h).blockTensor σ L v) =
      (∏ i, (inverseStandardCharacter ψ (m i) ⟨L i, hL i⟩ : ℂ)) * tensorContraction ell v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod,
      tensorContraction_tprod, smul_eq_mul, smul_eq_mul, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 2
    funext i
    exact hell i ⟨L i, hL i⟩ (v i)
  | add v v' hv hv' =>
    rw [map_add, map_add, hv, hv', map_add, mul_add]

/-- The inverse standard character of `n` is the product of the block characters of its
diagonal blocks and the inverse character of its corner entry `β_(m 0, 0)`. -/
theorem inverseStandardCharacter_eq_prod (n : upperUnipotent (t + 1) F) :
    (inverseStandardCharacter ψ t n : ℂ) =
      (∏ i, (inverseStandardCharacter ψ (m i)
        ⟨unipotentLevi h n i, unipotentLevi_mem h n i⟩ : ℂ)) *
        (ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0))⁻¹ := by
  rw [Fin.prod_univ_two, inverseStandardCharacter_apply, inverseStandardCharacter_apply,
    inverseStandardCharacter_apply, sum_superdiagonal_index h, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul]
  change ((ψ.complex (∑ k : Fin (m 0), unipotentLevi h n 0 k.castSucc k.succ) *
      ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0)) *
      ψ.complex (∑ k : Fin (m 1), unipotentLevi h n 1 k.castSucc k.succ))⁻¹ = _
  rw [mul_inv, mul_inv]
  ring

section Jacquet

variable [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]

/-- The coordinate change `x ↦ n_0⁻¹ (β + x n_1)` preserves every Borel additive Haar
measure on the upper radical. -/
theorem integral_comp_unipotentShift :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (n : upperUnipotent (t + 1) F)
      (G : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ),
      ∫ x, G (unipotentShift h n x) ∂μ = ∫ x, G x ∂μ := by
  intro _ μ _ n G
  have : MeasurableAdd (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (MeasurableAdd (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  let e := Shahidi.rectangularConj (unipotentLevi h n 0) (unipotentLevi h n 1)
  let c : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F :=
    ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) F).val * unipotentCorner h n
  have hμ : μ.map e = μ := by
    simpa only [determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 0),
      determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 1),
      Units.val_one, one_pow, div_one, one_smul] using
      Langlands.AllField.Shahidi.map_rectangularConj_padic F (⟨⟩ : LocalFieldData F) μ (unipotentLevi h n 0)
        (unipotentLevi h n 1)
  have hshift : ∀ x, unipotentShift h n x = c + e x := by
    intro x
    rw [unipotentShift, Shahidi.rectangularConj_apply, Matrix.mul_add, Matrix.mul_assoc]
  simp_rw [hshift]
  calc ∫ x, G (c + e x) ∂μ = ∫ y, G (c + y) ∂(μ.map e) :=
        (integral_map_equiv e (fun y => G (c + y))).symm
    _ = ∫ y, G (c + y) ∂μ := by rw [hμ]
    _ = ∫ y, G y ∂μ := integral_add_left_eq_self G c

variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- JPSS (4.6.2) at the identity is `ψ⁻¹`-equivariant under upper unipotent translation,
for every section: `J(ρ(n) f)(1) = ψ⁻¹(n) J(f)(1)`. This is a change of variables and
needs no integrability. -/
theorem jacquetFunction_inducedRep_upperUnipotent
    (hell : ∀ i, ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (n : upperUnipotent (t + 1) F) (f : Sections F h σ),
      jacquetFunction ψ ell μ (inducedRep F h σ n f) 1 =
        (inverseStandardCharacter ψ t n : ℂ) * jacquetFunction ψ ell μ f 1 := by
  intro _ μ _ n f
  let G : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun y =>
    tensorContraction ell (sectionEval F h σ f (upperRadical h F y * 1)) *
      ψ.complex (y (Fin.last (m 0)) 0)
  have hne : ψ.complex (unipotentCorner h n (Fin.last (m 0)) 0) ≠ 0 := by
    intro h0
    have h1 := ψ.norm_complex (unipotentCorner h n (Fin.last (m 0)) 0)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hpt : ∀ x,
      tensorContraction ell (sectionEval F h σ (inducedRep F h σ n f)
        (upperRadical h F x * 1)) * ψ.complex (x (Fin.last (m 0)) 0) =
        (inverseStandardCharacter ψ t n : ℂ) * G (unipotentShift h n x) := by
    intro x
    simp only [G, mul_one]
    change tensorContraction ell (radicalRestriction F h σ (inducedRep F h σ n f) x) * _ =
      _ * (tensorContraction ell (radicalRestriction F h σ f (unipotentShift h n x)) * _)
    rw [radicalRestriction_inducedRep, tensorContraction_blockTensor F h σ ψ ell hell _
      (unipotentLevi_mem h n), unipotentShift_last_zero, AddChar.map_add_eq_mul,
      inverseStandardCharacter_eq_prod F h ψ n]
    field_simp
  rw [jacquetFunction_apply, jacquetFunction_apply,
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_comp_unipotentShift F h μ n G]

omit [MeasurableAdd₂ F] [MeasurableMul F] in
/-- Sections with compact radical restriction have absolutely integrable JPSS integrand at
the identity, for every locally finite measure. -/
theorem isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule :
    ∀ [OpensMeasurableSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [IsFiniteMeasureOnCompacts μ] {f : Sections F h σ},
      f ∈ compactRadicalSubmodule F h σ → IsAbsIntegrableAt ψ ell μ f 1 := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ μ _ f hf
  have hc : Continuous (fun x => tensorContraction ell (radicalRestriction F h σ f x)) :=
    (((Induction.eval_isLocallyConstant _ _ f).comp (tensorContraction ell)).comp_continuous
      (continuous_upperRadical h F)).continuous
  have hs : HasCompactSupport (fun x => tensorContraction ell (radicalRestriction F h σ f x)) :=
    hf.comp_left (map_zero _)
  have hfun : integrand ψ ell f 1 =
      fun x => tensorContraction ell (radicalRestriction F h σ f x) * positiveKernel ψ x := by
    funext x
    rw [integrand_def, scalarSection_one, mul_one]
    rfl
  unfold IsAbsIntegrableAt
  rw [hfun]
  exact (hc.mul (continuous_positiveKernel ψ)).integrable_of_hasCompactSupport hs.mul_right

/-- JPSS (4.6.2) at the identity, as a linear functional on the compact-radical
sections, given integrability there. -/
def compactRadicalJacquet (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1) :
    compactRadicalSubmodule F h σ →ₗ[ℂ] ℂ where
  toFun f := jacquetFunction ψ ell μ f.val 1
  map_add' f f' := jacquetFunction_add ψ ell μ (hint f f.property) (hint f' f'.property)
  map_smul' c f := jacquetFunction_smul ψ ell μ c f.val 1

/-- The compact-radical functional is `ψ⁻¹`-equivariant under the upper unipotent group. -/
theorem compactRadicalJacquet_inducedRep
    (hell : ∀ i, ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (hint : ∀ f ∈ compactRadicalSubmodule F h σ, IsAbsIntegrableAt ψ ell μ f 1)
      (n : upperUnipotent (t + 1) F) (f : compactRadicalSubmodule F h σ),
      compactRadicalJacquet F h σ ψ ell μ hint
          ⟨inducedRep F h σ n f, inducedRep_mem_compactRadicalSubmodule F h σ n f.property⟩ =
        (inverseStandardCharacter ψ t n : ℂ) * compactRadicalJacquet F h σ ψ ell μ hint f := by
  intro _ μ _ hint n f
  exact jacquetFunction_inducedRep_upperUnipotent F h σ ψ ell hell μ n f.val

end Jacquet

end Contraction

end Sections

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
