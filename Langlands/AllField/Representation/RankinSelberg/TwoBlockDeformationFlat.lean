import Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
/-!
# Flat sections of the two-block deformation

For the lower block parabolic `Q̄` of `GL_(t+1)(F)` with blocks of sizes
`m 0 + 1` and `m 1 + 1`, and `K₀ = GL_(t+1)(O_F)`, every `g` factors as
`g = q k` with `q ∈ Q̄` and `k ∈ K₀`. The positive number
`κ(g) = |det q_0|`, the normalized absolute value of the determinant of the
first diagonal block of `q`, does not depend on the factorization. Multiplying
a section `f` of `ρ_0` by `κ(g)^u` gives a section `f_u` of `ρ_u`, and one
compact open subgroup fixes `f_u` for every complex `u`.
-/

noncomputable section

open scoped NNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen integralOpen inverseTranspose_mem_integralOpen isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos sectionEval_mul_flatStabilizer
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet

universe uF uW

section Iwasawa

variable (F : Type uF) [Field F]

/-- The hyperspecial subgroup `K₀ = GL_(n+1)(O_F)` of the canonical realization,
as an open subgroup. -/
def integralOpen [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    OpenSubgroup (GeneralLinear (n + 1) F) :=
  Conductor.levelOpenSubgroup F n 0

theorem mem_integralOpen [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} (k : GeneralLinear (n + 1) F) :
    k ∈ integralOpen F n ↔
      (∀ i j, k i j ∈ (⟨⟩ : LocalFieldData F).Integers) ∧
        (∀ i j, k⁻¹ i j ∈ (⟨⟩ : LocalFieldData F).Integers) := by
  change k ∈ Conductor.levelSubgroup F n 0 ↔ _
  rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]

theorem isCompact_integralOpen [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    IsCompact (integralOpen F n : Set (GeneralLinear (n + 1) F)) := by
  exact Conductor.isCompact_levelOpenSubgroup F n 0

/-- The inverse transpose of an integral matrix is integral. -/
theorem inverseTranspose_mem_integralOpen [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} {k : GeneralLinear (n + 1) F}
    (hk : k ∈ integralOpen F n) :
    inverseTranspose (n + 1) F k ∈ integralOpen F n := by
  rw [mem_integralOpen] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [inverseTranspose_entry]
    exact hk.2 j i
  · rw [← map_inv, inverseTranspose_entry, inv_inv]
    exact hk.1 j i

/-- An invertible matrix with zero entries above the diagonal lies in every lower block
parabolic. -/
theorem mem_oppositeParabolic_of_lower {n : ℕ} (B : BlockShape n)
    (g : GeneralLinear n F) (hg : ∀ a b : Fin n, a < b → g a b = 0) :
    g ∈ B.oppositeParabolic F := by
  rw [B.mem_oppositeParabolic_iff]
  intro i j a b hij
  exact hg _ _ (B.index_lt_index_of_block_lt hij a b)

/-- The lower Iwasawa decomposition `GL_(n+1)(F) = Q̄ K₀` for every block shape. -/
theorem exists_oppositeParabolic_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n : ℕ} (B : BlockShape (n + 1))
    (g : GeneralLinear (n + 1) F) :
    ∃ q ∈ B.oppositeParabolic F, ∃ k ∈ integralOpen F n, g = q * k := by
  obtain ⟨k, hk, hup⟩ := Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F)
    (n + 1) (inverseTranspose (n + 1) F g)
  have hk' : k ∈ integralOpen F n := by
    rw [mem_integralOpen]
    exact (Conductor.mem_integralSubgroup _ n k).mp hk
  set b := inverseTranspose (n + 1) F g * k with hb
  have hbinv : (b⁻¹).val.IsUpperTriangular :=
    (upperTriangularSubgroup (n + 1) F).inv_mem (show b ∈ _ from hup)
  refine ⟨inverseTranspose (n + 1) F b, ?_,
    (inverseTranspose (n + 1) F k)⁻¹,
    inv_mem (inverseTranspose_mem_integralOpen F hk'), ?_⟩
  · apply mem_oppositeParabolic_of_lower
    intro a c hac
    rw [inverseTranspose_entry]
    exact hbinv hac
  · rw [hb, map_mul, inverseTranspose_involutive, mul_inv_cancel_right]

end Iwasawa

section BlockNorm

variable (F : Type uF) [Field F]
variable {n : ℕ} (B : BlockShape (n + 1)) (i : Fin B.length)

/-- An invertible matrix whose entries and inverse entries are integral has
determinant of normalized absolute value one. -/
private theorem determinantNorm_eq_one_of_integral [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {r : ℕ} (g : GeneralLinear r F)
    (hg : ∀ a b, g a b ∈ (⟨⟩ : LocalFieldData F).Integers)
    (hginv : ∀ a b, g⁻¹ a b ∈ (⟨⟩ : LocalFieldData F).Integers) :
    (⟨⟩ : LocalFieldData F).determinantNorm r g = 1 := by
  set T := (⟨⟩ : LocalFieldData F)
  have hdet : ∀ h : GeneralLinear r F, (∀ a b, h a b ∈ T.Integers) →
      (GeneralLinear.determinant h : F) ∈ T.Integers := by
    intro h hh
    let M : Matrix (Fin r) (Fin r) T.Integers := Matrix.of fun a b => ⟨h a b, hh a b⟩
    have hM : T.Integers.subtype.mapMatrix M = h.val := by
      ext a b
      rfl
    have he : (GeneralLinear.determinant h : F) = T.Integers.subtype M.det := by
      rw [RingHom.map_det, hM, Matrix.GeneralLinearGroup.val_det_apply]
    rw [he]
    exact M.det.property
  have h1 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g hg)
  have h2 := (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hdet g⁻¹ hginv)
  have hprod : T.normalizedAbs (GeneralLinear.determinant g : F) *
      T.normalizedAbs (GeneralLinear.determinant g⁻¹ : F) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hnn := T.normalizedAbs_nonneg (GeneralLinear.determinant g : F)
  have hnn' := T.normalizedAbs_nonneg (GeneralLinear.determinant g⁻¹ : F)
  have heq : T.normalizedAbs (GeneralLinear.determinant g : F) = 1 := by
    nlinarith
  apply Units.ext
  apply NNReal.eq
  rw [T.determinantNorm_coe]
  simpa using heq

/-- The diagonal blocks of an element of `Q̄ ∩ K₀` have determinant of absolute value one. -/
theorem determinantNorm_oppositeLeviProjection_of_mem [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (r : B.oppositeParabolic F)
    (hr : (r : GeneralLinear (n + 1) F) ∈ integralOpen F n) :
    (⟨⟩ : LocalFieldData F).determinantNorm (B.size i)
      (B.oppositeLeviProjection F r i) = 1 := by
  rw [mem_integralOpen] at hr
  apply determinantNorm_eq_one_of_integral F
  · intro a b
    rw [BlockShape.oppositeLeviProjection_apply]
    exact hr.1 _ _
  · intro a b
    rw [← Pi.inv_apply, ← map_inv, BlockShape.oppositeLeviProjection_apply]
    exact hr.2 _ _

/-- The norm `|det q_i|` of the `i`th diagonal block of the lower parabolic factor `q`
of `g = q k`, `k ∈ K₀`. -/
def oppositeBlockNorm [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (n + 1) F) : ℝ :=
  (((⟨⟩ : LocalFieldData F).determinantNorm (B.size i)
    (B.oppositeLeviProjection F
      ⟨(exists_oppositeParabolic_mul F B g).choose,
        (exists_oppositeParabolic_mul F B g).choose_spec.1⟩ i) : ℝ≥0) : ℝ)

/-- The block norm can be computed from any lower Iwasawa factorization. -/
theorem oppositeBlockNorm_eq [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : B.oppositeParabolic F)
    {k : GeneralLinear (n + 1) F} (hk : k ∈ integralOpen F n)
    {g : GeneralLinear (n + 1) F} (hg : g = q * k) :
    oppositeBlockNorm F B i g =
      (((⟨⟩ : LocalFieldData F).determinantNorm (B.size i)
        (B.oppositeLeviProjection F q i) : ℝ≥0) : ℝ) := by
  obtain ⟨hq', k', hk', hg'⟩ := (exists_oppositeParabolic_mul F B g).choose_spec
  set q' : B.oppositeParabolic F :=
    ⟨(exists_oppositeParabolic_mul F B g).choose, hq'⟩ with hq'def
  change (((⟨⟩ : LocalFieldData F).determinantNorm (B.size i)
    (B.oppositeLeviProjection F q' i) : ℝ≥0) : ℝ) = _
  have hg'' : g = (q' : GeneralLinear (n + 1) F) * k' := hg'
  set r : B.oppositeParabolic F := q⁻¹ * q' with hr
  have hrval : (r : GeneralLinear (n + 1) F) = k * k'⁻¹ := by
    rw [hr, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, ← hg, ← hg'']
  have hrmem : (r : GeneralLinear (n + 1) F) ∈ integralOpen F n := by
    rw [hrval]
    exact mul_mem hk (inv_mem hk')
  have hq'r : q' = q * r := by
    rw [hr, mul_inv_cancel_left]
  rw [hq'r, map_mul, Pi.mul_apply, map_mul,
    determinantNorm_oppositeLeviProjection_of_mem F B i r hrmem, mul_one]

theorem oppositeBlockNorm_pos [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (n + 1) F) :
    0 < oppositeBlockNorm F B i g := by
  unfold oppositeBlockNorm
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))

/-- Right invariance under `K₀`. -/
theorem oppositeBlockNorm_mul_integral [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (n + 1) F)
    {k : GeneralLinear (n + 1) F} (hk : k ∈ integralOpen F n) :
    oppositeBlockNorm F B i (g * k) = oppositeBlockNorm F B i g := by
  obtain ⟨q, hq, k₁, hk₁, hg⟩ := exists_oppositeParabolic_mul F B g
  rw [oppositeBlockNorm_eq F B i ⟨q, hq⟩ hk₁ hg,
    oppositeBlockNorm_eq F B i ⟨q, hq⟩ (mul_mem hk₁ hk) (by rw [hg, mul_assoc])]

/-- Left covariance under the lower parabolic. -/
theorem oppositeBlockNorm_oppositeParabolic_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (q : B.oppositeParabolic F)
    (g : GeneralLinear (n + 1) F) :
    oppositeBlockNorm F B i ((q : GeneralLinear (n + 1) F) * g) =
      (((⟨⟩ : LocalFieldData F).determinantNorm (B.size i)
        (B.oppositeLeviProjection F q i) : ℝ≥0) : ℝ) * oppositeBlockNorm F B i g := by
  obtain ⟨q₁, hq₁, k₁, hk₁, hg⟩ := exists_oppositeParabolic_mul F B g
  rw [oppositeBlockNorm_eq F B i ⟨q₁, hq₁⟩ hk₁ hg,
    oppositeBlockNorm_eq F B i (q * ⟨q₁, hq₁⟩) hk₁ (by rw [hg, Subgroup.coe_mul, mul_assoc]),
    map_mul, Pi.mul_apply, map_mul, Units.val_mul, NNReal.coe_mul]

/-- The block norm is locally constant, being right invariant under the open subgroup `K₀`. -/
theorem isLocallyConstant_oppositeBlockNorm [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsLocallyConstant (oppositeBlockNorm F B i) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (integralOpen F n : Set (GeneralLinear (n + 1) F)),
    isOpenMap_mul_left x _ (integralOpen F n).isOpen, ⟨1, one_mem _, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact oppositeBlockNorm_mul_integral F B i x hk

end BlockNorm

section Flat

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- `κ(qk) = |det q_0|`: the first-block norm of the lower Iwasawa factor. -/
def blockZeroNorm [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) : ℝ :=
  oppositeBlockNorm F (succBlockShape m h) 0 g

theorem blockZeroNorm_pos [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) : 0 < blockZeroNorm F h g :=
  oppositeBlockNorm_pos F _ 0 g

theorem blockZeroNorm_mul_integral [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F)
    {k : GeneralLinear (t + 1) F} (hk : k ∈ integralOpen F t) :
    blockZeroNorm F h (g * k) = blockZeroNorm F h g :=
  oppositeBlockNorm_mul_integral F _ 0 g hk

theorem blockZeroNorm_oppositeParabolic_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (q : (succBlockShape m h).oppositeParabolic F) (g : GeneralLinear (t + 1) F) :
    blockZeroNorm F h ((q : GeneralLinear (t + 1) F) * g) =
      (((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1)
        ((succBlockShape m h).oppositeLeviProjection F q 0) : ℝ≥0) : ℝ) *
        blockZeroNorm F h g :=
  oppositeBlockNorm_oppositeParabolic_mul F _ 0 q g

theorem isLocallyConstant_blockZeroNorm [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsLocallyConstant (blockZeroNorm F h) :=
  isLocallyConstant_oppositeBlockNorm F _ 0

variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- The block tensor of the deformed blocks differs from the undeformed one by
`|det a_0|^u`. -/
theorem blockTensor_twoBlockDeformedBlocks [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ) (a : (succBlockShape m h).Levi F) :
    (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u) a =
      (((⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) u (a 0) : ℂˣ) : ℂ) •
        (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0) a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.smul_apply]
  erw [BlockShape.blockTensor_tprod, BlockShape.blockTensor_tprod]
  change PiTensorProduct.tprod ℂ (fun i =>
      (((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then u else 0) (a i) : ℂˣ) : ℂ) • σ i (a i) (v i)) =
    (((⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) u (a 0) : ℂˣ) : ℂ) •
      PiTensorProduct.tprod ℂ (fun i =>
      (((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then (0 : ℂ) else 0) (a i) : ℂˣ) : ℂ) • σ i (a i) (v i))
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ, (PiTensorProduct.tprod ℂ).map_smul_univ,
    smul_smul]
  congr 1
  simp [Fin.prod_univ_two]

/-- The underlying function `g ↦ κ(g)^u f(g)` of a flat section. -/
def flatFunction [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ) (f : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (g : GeneralLinear (t + 1) F) : PiTensorProduct ℂ W :=
  ((blockZeroNorm F h g : ℂ) ^ u) • sectionEval F h _ f g

theorem flatFunction_covariant [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ) (f : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (q : (succBlockShape m h).oppositeParabolic F) (x : GeneralLinear (t + 1) F) :
    flatFunction F h σ u f ((q : GeneralLinear (t + 1) F) * x) =
      (twist ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
        (((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u)).comp
          ((succBlockShape m h).oppositeLeviProjection F))) q
        (flatFunction F h σ u f x) := by
  have hf := f.1.2 q x
  change sectionEval F h _ f ((q : GeneralLinear (t + 1) F) * x) =
    (twist ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0)).comp
        ((succBlockShape m h).oppositeLeviProjection F))) q (sectionEval F h _ f x) at hf
  unfold flatFunction
  rw [hf, blockZeroNorm_oppositeParabolic_mul]
  change _ = (((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
      ℂˣ) : ℂ) • (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ u)
        ((succBlockShape m h).oppositeLeviProjection F q) _
  change _ • ((((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
      ℂˣ) : ℂ) • (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0)
        ((succBlockShape m h).oppositeLeviProjection F q) _) = _
  rw [blockTensor_twoBlockDeformedBlocks F h σ u, LinearMap.smul_apply, map_smul,
    Langlands.LocalFieldData.determinantComplexPower_apply,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _)
      (blockZeroNorm_pos F h x).le]
  simp only [smul_smul]
  congr 1
  ring

/-- The uniform stabilizer of the flat family through `f`: a chosen open stabilizer of `f`,
intersected with `K₀`. -/
def flatStabilizer [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    OpenSubgroup (GeneralLinear (t + 1) F) :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  have hf : ∃ K : OpenSubgroup (GeneralLinear (t + 1) F),
      f.1 ∈ fixedVectors (Induction.equivariantAction _ _) K.toSubgroup := f.property
  Classical.choose hf ⊓ integralOpen F t

theorem flatStabilizer_le_integralOpen [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    flatStabilizer F h σ f ≤ integralOpen F t := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  exact inf_le_right

theorem sectionEval_mul_flatStabilizer [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (x : GeneralLinear (t + 1) F) {k : GeneralLinear (t + 1) F}
    (hk : k ∈ flatStabilizer F h σ f) :
    sectionEval F h _ f (x * k) = sectionEval F h _ f x := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  have hf : ∃ K : OpenSubgroup (GeneralLinear (t + 1) F),
      f.1 ∈ fixedVectors (Induction.equivariantAction _ _) K.toSubgroup := f.property
  have hK := Classical.choose_spec hf ⟨k, hk.1⟩
  exact congrArg (fun F' : Induction.EquivariantFunctions _ _ => F'.1 x) hK

theorem flatFunction_mul_flatStabilizer [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ)
    (f : Sections F h (twoBlockDeformedBlocks F m σ 0))
    (x : GeneralLinear (t + 1) F) {k : GeneralLinear (t + 1) F}
    (hk : k ∈ flatStabilizer F h σ f) :
    flatFunction F h σ u f (x * k) = flatFunction F h σ u f x := by
  unfold flatFunction
  rw [sectionEval_mul_flatStabilizer F h σ f x hk,
    blockZeroNorm_mul_integral F h x (flatStabilizer_le_integralOpen F h σ f hk)]

/-- The flat section `f_u(g) = κ(g)^u f(g)` of `ρ_u` through a section `f` of `ρ_0`. -/
def flatSection [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ) :
    Sections F h (twoBlockDeformedBlocks F m σ 0) →ₗ[ℂ]
      Sections F h (twoBlockDeformedBlocks F m σ u) where
  toFun f :=
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
    Induction.smoothFunctionOf _ _ (flatFunction F h σ u f) (flatFunction_covariant F h σ u f)
      (flatStabilizer F h σ f) (fun k x => flatFunction_mul_flatStabilizer F h σ u f x k.2)
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact smul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact smul_comm ((blockZeroNorm F h x : ℂ) ^ u) c (sectionEval F h _ f x)

theorem flatSection_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    flatSection F h σ 0 f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ((blockZeroNorm F h x : ℂ) ^ (0 : ℂ)) • sectionEval F h _ f x = sectionEval F h _ f x
  rw [Complex.cpow_zero, one_smul]

/-- One compact open subgroup fixes every member of the flat family through `f`. -/
theorem exists_uniform_stabilizer [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : Sections F h (twoBlockDeformedBlocks F m σ 0)) :
    ∃ K : Subgroup (GeneralLinear (t + 1) F),
      IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
          ∀ (u : ℂ) (k : K), inducedRep F h (twoBlockDeformedBlocks F m σ u) k
            (flatSection F h σ u f) = flatSection F h σ u f := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  refine ⟨(flatStabilizer F h σ f).toSubgroup, (flatStabilizer F h σ f).isOpen,
    (isCompact_integralOpen F t).of_isClosed_subset (flatStabilizer F h σ f).isClosed
      (flatStabilizer_le_integralOpen F h σ f), fun u k => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact flatFunction_mul_flatStabilizer F h σ u f x k.2

end Flat

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
