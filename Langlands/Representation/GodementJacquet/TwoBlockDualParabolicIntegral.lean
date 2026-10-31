import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.PadicLatticeTopology
import Langlands.Group.GL.Maps
import Langlands.HarmonicAnalysis.TwoBlockPartialFourier
import Langlands.Representation.Hecke.TestFunction
import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate

/-!
# The dual two-block parabolic integral

Godement–Jacquet 1972, proof of Theorem 3.4 (printed pages 36–45): after the
substitution `g ↦ (g⁻¹)ᵀ`, the transformed zeta integral of an induced
representation is reduced to the Levi blocks along the coordinates
`(a, d, x) ↦ [[a, a x], [0, d]]` of the upper block parabolic. The inverse
transpose of this matrix is `[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]`, so the
radical variable `x` enters through the lower-left block. The substitution
`C = -(d⁻¹)ᵀ xᵀ` multiplies the rectangular Haar measure by `|det d|^(n₀)`, and
the lower-left partial integral of the test function then splits into the
Levi blocks.

This module proves that reduction for a test function whose lower-left partial
integral is a finite sum of tensor products, with weights `u₀, u₁` on the two
Levi blocks that are integrable against every Schwartz–Bruhat function composed
with the inverse transpose. Integrability on the product space comes from a
majorant by a product of indicators of compact open sets. The reduction is stated
both in the coordinates `((a, d), x)` and in Levi coordinates `(L, x)`. A last
section transfers finite decompositions of two-sided compact translates of a test
function to its Fourier transform evaluated at inverse transposes.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg
open HarmonicAnalysis (blockMatrix)
open scoped NNReal ENNReal

universe uF

section Transpose

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

omit [AddGroup F] [TopologicalSpace F] in
theorem measurable_matrix_transpose {r s : ℕ} :
    Measurable (Matrix.transpose : Matrix (Fin r) (Fin s) F → Matrix (Fin s) (Fin r) F) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply

/-- Transpose as a measurable equivalence of rectangular matrix spaces. -/
def transposeMeasurableEquiv (r s : ℕ) :
    Matrix (Fin r) (Fin s) F ≃ᵐ Matrix (Fin s) (Fin r) F where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  measurable_toFun := measurable_matrix_transpose
  measurable_invFun := measurable_matrix_transpose

/-- Transposition carries the rectangular product measure on `r × s` matrices to
the one on `s × r` matrices. -/
theorem measurePreserving_transpose_rectangularMeasure (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure] (r s : ℕ) :
    MeasurePreserving (transposeMeasurableEquiv (F := F) r s)
      (rectangularMeasure ν r s) (rectangularMeasure ν s r) := by
  refine ⟨measurable_matrix_transpose, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun _ : Fin s => Set.pi Set.univ '' Set.pi Set.univ
      fun _ : Fin r => {t : Set F | MeasurableSet t})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => ν.measure.toFiniteSpanningSetsIn) ?_
  intro S hS
  choose t ht hSt using hS
  obtain rfl : S = fun j => Set.pi Set.univ (t j) := funext fun j => (hSt j).symm
  have hmeasS : MeasurableSet
      (Set.pi Set.univ (fun j => Set.pi Set.univ (t j)) : Set (Matrix (Fin s) (Fin r) F)) :=
    MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi fun i => ht j i (Set.mem_univ i)
  have hmap := Measure.map_apply (μ := rectangularMeasure ν r s)
    (measurable_matrix_transpose (F := F) (r := r) (s := s)) hmeasS
  have hpre : (Matrix.transpose ⁻¹'
      (Set.pi Set.univ (fun j => Set.pi Set.univ (t j)) : Set (Matrix (Fin s) (Fin r) F)) :
        Set (Matrix (Fin r) (Fin s) F)) =
      Set.pi Set.univ fun i : Fin r => Set.pi Set.univ fun j : Fin s => t j i := by
    ext x
    exact ⟨fun h i _ j _ => h j trivial i trivial, fun h j _ i _ => h i trivial j trivial⟩
  refine hmap.trans ?_
  rw [hpre]
  change Measure.pi (fun _ : Fin r => Measure.pi (fun _ : Fin s => ν.measure)) _ = _
  simp only [Measure.pi_pi]
  exact Finset.prod_comm

end Transpose

section BlockAlgebra

variable {R : Type uF} [CommRing R] {n0 n1 N : ℕ}

/-- The inverse transpose of an upper block matrix `[[a, a x], [0, d]]` is
`[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]`. -/
theorem inverseTranspose_val_of_upperBlock (e : Fin n0 ⊕ Fin n1 ≃ Fin N)
    (g : Langlands.GeneralLinear N R) (a : Langlands.GeneralLinear n0 R)
    (d : Langlands.GeneralLinear n1 R) (x : Matrix (Fin n0) (Fin n1) R)
    (hg : g.val = Matrix.reindex e e (Matrix.fromBlocks a.val (a.val * x) 0 d.val)) :
    (GeneralLinear.inverseTranspose N R g).val =
      Matrix.reindex e e (Matrix.fromBlocks (GeneralLinear.inverseTranspose n0 R a).val 0
        (-((GeneralLinear.inverseTranspose n1 R d).val * x.transpose))
        (GeneralLinear.inverseTranspose n1 R d).val) := by
  set Minv : Matrix (Fin N) (Fin N) R := Matrix.reindex e e
    (Matrix.fromBlocks (a⁻¹ : Langlands.GeneralLinear n0 R).val
      (-(x * (d⁻¹ : Langlands.GeneralLinear n1 R).val)) 0
      (d⁻¹ : Langlands.GeneralLinear n1 R).val) with hMinv
  have hmul : g.val * Minv = 1 := by
    rw [hg, hMinv, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply]
    have h1 : a.val * (a⁻¹ : Langlands.GeneralLinear n0 R).val = 1 := Units.mul_inv a
    have h2 : d.val * (d⁻¹ : Langlands.GeneralLinear n1 R).val = 1 := Units.mul_inv d
    have h3 : a.val * -(x * (d⁻¹ : Langlands.GeneralLinear n1 R).val) +
        a.val * x * (d⁻¹ : Langlands.GeneralLinear n1 R).val = 0 := by
      rw [Matrix.mul_neg, Matrix.mul_assoc, neg_add_cancel]
    simp only [h1, h2, h3, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hinv : (g⁻¹ : Langlands.GeneralLinear N R).val = Minv := by
    calc (g⁻¹ : Langlands.GeneralLinear N R).val
        = (g⁻¹ : Langlands.GeneralLinear N R).val * (g.val * Minv) := by rw [hmul, Matrix.mul_one]
      _ = Minv := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [GeneralLinear.inverseTranspose_coe, hinv, hMinv, Matrix.transpose_reindex,
    Matrix.fromBlocks_transpose]
  simp only [GeneralLinear.inverseTranspose_coe, Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_zero]

end BlockAlgebra

section Majorant

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

/-- Every compact subset of a locally compact Hausdorff totally disconnected space
lies in a compact clopen set. -/
theorem exists_isCompact_isClopen_superset {S : Set X} (hS : IsCompact S) :
    ∃ U : Set X, IsCompact U ∧ IsClopen U ∧ S ⊆ U := by
  choose U hUc hUo hxU _ using fun x : X =>
    HarmonicAnalysis.exists_compact_clopen (x := x) (V := Set.univ) Filter.univ_mem
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover U (fun x => (hUo x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  exact ⟨⋃ x ∈ s, U x, s.isCompact_biUnion fun x _ => hUc x,
    s.finite_toSet.isClopen_biUnion fun x _ => hUo x, hs⟩

end Majorant

section BlockMajorant

variable {K : Type uF} [TopologicalSpace K] [Zero K] [T2Space K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K] {n0 n1 N : ℕ} (e : Fin n0 ⊕ Fin n1 ≃ Fin N)

/-- A Schwartz–Bruhat function of a block matrix `[[A, 0], [C, D]]` is bounded by a
constant times a product of Schwartz–Bruhat functions of the three blocks (indicators of
compact clopen sets). -/
theorem exists_blockMatrix_majorant (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)) :
    ∃ (M : ℝ) (bA : SchwartzBruhat (Matrix (Fin n0) (Fin n0) K))
      (bC : SchwartzBruhat (Matrix (Fin n1) (Fin n0) K))
      (bD : SchwartzBruhat (Matrix (Fin n1) (Fin n1) K)),
      ∀ A C D, ‖Φ (blockMatrix e A 0 C D)‖ ≤ M * (‖bA A‖ * ‖bC C‖ * ‖bD D‖) := by
  have : ∀ a b : ℕ, LocallyCompactSpace (Matrix (Fin a) (Fin b) K) := fun a b =>
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → K))
  have : ∀ a b : ℕ, TotallyDisconnectedSpace (Matrix (Fin a) (Fin b) K) := fun a b =>
    inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin b → K))
  obtain ⟨M, hM⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hK : IsCompact (tsupport (Φ : Matrix (Fin N) (Fin N) K → ℂ)) := Φ.hasCompactSupport
  obtain ⟨UA, hUAc, hUAo, hUA⟩ := exists_isCompact_isClopen_superset
    (hK.image (continuous_id.matrix_submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)))
  obtain ⟨UC, hUCc, hUCo, hUC⟩ := exists_isCompact_isClopen_superset
    (hK.image (continuous_id.matrix_submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)))
  obtain ⟨UD, hUDc, hUDo, hUD⟩ := exists_isCompact_isClopen_superset
    (hK.image (continuous_id.matrix_submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)))
  refine ⟨M, Hecke.TestFunction.characteristic hUAo hUAc,
    Hecke.TestFunction.characteristic hUCo hUCc,
    Hecke.TestFunction.characteristic hUDo hUDc, fun A C D => ?_⟩
  by_cases h : blockMatrix e A 0 C D ∈ tsupport (Φ : Matrix (Fin N) (Fin N) K → ℂ)
  · have hA : A ∈ UA := hUA ⟨_, h, by ext i j; simp [blockMatrix_apply]⟩
    have hC : C ∈ UC := hUC ⟨_, h, by ext i j; simp [blockMatrix_apply]⟩
    have hD : D ∈ UD := hUD ⟨_, h, by ext i j; simp [blockMatrix_apply]⟩
    simp only [Hecke.TestFunction.characteristic_apply, Set.indicator_of_mem hA,
      Set.indicator_of_mem hC, Set.indicator_of_mem hD, norm_one, mul_one]
    exact hM _
  · rw [image_eq_zero_of_notMem_tsupport h, norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hM 0)) (by positivity)

end BlockMajorant

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualParabolicTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualParabolicValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualParabolicLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualParabolicMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance dualParabolicBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualParabolicSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance dualParabolicT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance dualParabolicTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance dualParabolicMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance dualParabolicGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n F.Carrier) := borel _
local instance dualParabolicGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- Left multiplication by an invertible matrix, as a measurable equivalence of
rectangular matrices. -/
def mulLeftMeasurableEquiv {r : ℕ} (A : Langlands.GeneralLinear r F.Carrier) (s : ℕ) :
    Matrix (Fin r) (Fin s) F.Carrier ≃ᵐ Matrix (Fin r) (Fin s) F.Carrier :=
  Homeomorph.toMeasurableEquiv
    { toFun := fun X => A.val * X
      invFun := fun X => (A⁻¹ : Langlands.GeneralLinear r F.Carrier).val * X
      left_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }

theorem mulLeftMeasurableEquiv_apply {r : ℕ} (A : Langlands.GeneralLinear r F.Carrier)
    (s : ℕ) (X : Matrix (Fin r) (Fin s) F.Carrier) :
    mulLeftMeasurableEquiv F A s X = A.val * X := rfl

/-- Left multiplication by `A` scales the rectangular measure by `|det A|^(-s)`. -/
theorem map_mulLeftMeasurableEquiv (ν : AdditiveHaarMeasure F.Carrier) {r : ℕ}
    (A : Langlands.GeneralLinear r F.Carrier) (s : ℕ) :
    (rectangularMeasure ν r s).map (mulLeftMeasurableEquiv F A s) =
      ((F.canonicalTopologicalData.determinantNorm r A : ℝ≥0) ^ s)⁻¹ •
        rectangularMeasure ν r s := by
  have h := padicRectangularHaarScaling F F.canonicalTopologicalData r s
    (rectangularMeasure ν r s) A 1
  simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, one_pow, div_one] at h
  exact h

/-- The lower-left substitution `C = -((d⁻¹)ᵀ xᵀ)` multiplies the rectangular measure
by `|det d|^(n₀)`. -/
theorem integral_comp_lowerLeft {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : AdditiveHaarMeasure F.Carrier) {n0 n1 : ℕ} (d : Langlands.GeneralLinear n1 F.Carrier)
    (G : Matrix (Fin n1) (Fin n0) F.Carrier → E) :
    ∫ x, G (-((GeneralLinear.inverseTranspose n1 F.Carrier d).val * x.transpose))
        ∂rectangularMeasure ν n0 n1 =
      (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det ^ n0) •
        ∫ C, G C ∂rectangularMeasure ν n1 n0 := by
  set A : Langlands.GeneralLinear n1 F.Carrier :=
    -GeneralLinear.inverseTranspose n1 F.Carrier d with hAdef
  have hA : ∀ y, mulLeftMeasurableEquiv F A n0 y =
      -((GeneralLinear.inverseTranspose n1 F.Carrier d).val * y) := fun y => by
    rw [mulLeftMeasurableEquiv_apply, hAdef, Units.val_neg, Matrix.neg_mul]
  have hdet : ((F.canonicalTopologicalData.determinantNorm n1 A : ℝ≥0) : ℝ) =
      (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det)⁻¹ := by
    rw [PadicField.TopologicalData.determinantNorm_coe]
    change normalizedAbsoluteValue F.canonicalTopologicalData
      ((GeneralLinear.determinant A : F.Carrierˣ) : F.Carrier) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, hAdef, Units.val_neg, Matrix.det_neg,
      AbsoluteValue.map_mul, AbsoluteValue.map_pow, AbsoluteValue.map_neg,
      AbsoluteValue.map_one, one_pow, one_mul, abv_det_inverseTranspose]
  calc ∫ x, G (-((GeneralLinear.inverseTranspose n1 F.Carrier d).val * x.transpose))
        ∂rectangularMeasure ν n0 n1
      = ∫ x, (fun y => G (mulLeftMeasurableEquiv F A n0 y))
          (transposeMeasurableEquiv n0 n1 x) ∂rectangularMeasure ν n0 n1 := by
        simp only [hA]
        rfl
    _ = ∫ y, G (mulLeftMeasurableEquiv F A n0 y) ∂rectangularMeasure ν n1 n0 :=
        (measurePreserving_transpose_rectangularMeasure ν n0 n1).integral_comp'
          (fun y => G (mulLeftMeasurableEquiv F A n0 y))
    _ = ∫ C, G C ∂((rectangularMeasure ν n1 n0).map (mulLeftMeasurableEquiv F A n0)) :=
        (integral_map_equiv _ G).symm
    _ = _ := by
        rw [map_mulLeftMeasurableEquiv, integral_smul_nnreal_measure, NNReal.smul_def]
        congr 1
        rw [NNReal.coe_inv, NNReal.coe_pow, hdet, inv_pow, inv_inv]

/-- Integrability is preserved by the lower-left substitution. -/
theorem integrable_comp_lowerLeft {E : Type*} [NormedAddCommGroup E]
    (ν : AdditiveHaarMeasure F.Carrier) {n0 n1 : ℕ} (d : Langlands.GeneralLinear n1 F.Carrier)
    {G : Matrix (Fin n1) (Fin n0) F.Carrier → E}
    (hG : Integrable G (rectangularMeasure ν n1 n0)) :
    Integrable (fun x => G (-((GeneralLinear.inverseTranspose n1 F.Carrier d).val *
      x.transpose))) (rectangularMeasure ν n0 n1) := by
  set A : Langlands.GeneralLinear n1 F.Carrier :=
    -GeneralLinear.inverseTranspose n1 F.Carrier d with hAdef
  have hA : ∀ y, mulLeftMeasurableEquiv F A n0 y =
      -((GeneralLinear.inverseTranspose n1 F.Carrier d).val * y) := fun y => by
    rw [mulLeftMeasurableEquiv_apply, hAdef, Units.val_neg, Matrix.neg_mul]
  have h1 : Integrable G ((rectangularMeasure ν n1 n0).map (mulLeftMeasurableEquiv F A n0)) := by
    rw [map_mulLeftMeasurableEquiv]
    exact hG.smul_measure_nnreal
  have h2 := (integrable_map_equiv _ G).mp h1
  have h3 := ((measurePreserving_transpose_rectangularMeasure ν n0 n1).integrable_comp_emb
    (transposeMeasurableEquiv n0 n1).measurableEmbedding).mpr h2
  convert h3 using 2 with x
  simp only [Function.comp_apply, hA]
  rfl

section DualParabolic

variable {n0 n1 N : ℕ} (e : Fin n0 ⊕ Fin n1 ≃ Fin N)

/-- The transformed integrand `Φ ([[a, a x], [0, d]]⁻ᵀ) u₀(a) u₁(d)` in the coordinates
`((a, d), x)`, written through the block form
`[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]` of the inverse transpose. -/
def dualParabolicIntegrand (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F.Carrier))
    (u0 : Langlands.GeneralLinear n0 F.Carrier → ℂ)
    (u1 : Langlands.GeneralLinear n1 F.Carrier → ℂ)
    (z : (Langlands.GeneralLinear n0 F.Carrier × Langlands.GeneralLinear n1 F.Carrier) ×
      Matrix (Fin n0) (Fin n1) F.Carrier) : ℂ :=
  Φ (blockMatrix e (GeneralLinear.inverseTranspose n0 F.Carrier z.1.1).val 0
      (-((GeneralLinear.inverseTranspose n1 F.Carrier z.1.2).val * z.2.transpose))
      (GeneralLinear.inverseTranspose n1 F.Carrier z.1.2).val) * u0 z.1.1 * u1 z.1.2

theorem measurable_inverseTranspose_val (n : ℕ) :
    Measurable fun a : Langlands.GeneralLinear n F.Carrier =>
      (GeneralLinear.inverseTranspose n F.Carrier a).val :=
  (Units.continuous_val.comp (GeneralLinear.continuous_inverseTranspose n F.Carrier)).measurable

/-- The transformed integrand is a.e. strongly measurable for every product measure
for which the two Levi weights are. -/
theorem aestronglyMeasurable_dualParabolicIntegrand (ν : AdditiveHaarMeasure F.Carrier)
    {μ0 : Measure (Langlands.GeneralLinear n0 F.Carrier)}
    {μ1 : Measure (Langlands.GeneralLinear n1 F.Carrier)} [SFinite μ0] [SFinite μ1]
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F.Carrier))
    {u0 : Langlands.GeneralLinear n0 F.Carrier → ℂ}
    {u1 : Langlands.GeneralLinear n1 F.Carrier → ℂ}
    (hu0m : AEStronglyMeasurable u0 μ0) (hu1m : AEStronglyMeasurable u1 μ1) :
    AEStronglyMeasurable (dualParabolicIntegrand F e Φ u0 u1)
      ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) := by
  have hblk : Continuous fun w : Matrix (Fin n0) (Fin n0) F.Carrier ×
      Matrix (Fin n1) (Fin n0) F.Carrier × Matrix (Fin n1) (Fin n1) F.Carrier =>
        blockMatrix e w.1 0 w.2.1 w.2.2 :=
    (continuous_fst.matrix_fromBlocks continuous_const (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).matrix_reindex e e
  have hT0 := measurable_inverseTranspose_val F n0
  have hT1 := measurable_inverseTranspose_val F n1
  have hψ : Measurable fun z : (Langlands.GeneralLinear n0 F.Carrier ×
      Langlands.GeneralLinear n1 F.Carrier) × Matrix (Fin n0) (Fin n1) F.Carrier =>
        ((GeneralLinear.inverseTranspose n0 F.Carrier z.1.1).val,
          -((GeneralLinear.inverseTranspose n1 F.Carrier z.1.2).val * z.2.transpose),
          (GeneralLinear.inverseTranspose n1 F.Carrier z.1.2).val) :=
    (hT0.comp (measurable_fst.comp measurable_fst)).prodMk
      ((((continuous_fst.matrix_mul continuous_snd.matrix_transpose).neg).measurable.comp
        ((hT1.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (hT1.comp (measurable_snd.comp measurable_fst)))
  have hΦ := ((Φ.continuous.comp hblk).stronglyMeasurable.comp_measurable hψ).aestronglyMeasurable
    (μ := (μ0.prod μ1).prod (rectangularMeasure ν n0 n1))
  exact (hΦ.mul hu0m.comp_fst.comp_fst).mul hu1m.comp_snd.comp_fst

/-- **Dual parabolic reduction.** Suppose the lower-left partial integral of `Φ` is a
finite sum of tensor products `∑ₖ αₖ(x) βₖ(y)`, and that `a ↦ Ψ((a⁻¹)ᵀ) u₀(a)` and
`d ↦ Ψ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀)` are integrable for every Schwartz–Bruhat `Ψ`.
Then the transformed integrand is integrable on `(GL_{n₀} × GL_{n₁}) × M_{n₀×n₁}`, and its
integral is `∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀) dd)`. -/
theorem integrable_integral_dualParabolicIntegrand (ν : AdditiveHaarMeasure F.Carrier)
    {μ0 : Measure (Langlands.GeneralLinear n0 F.Carrier)}
    {μ1 : Measure (Langlands.GeneralLinear n1 F.Carrier)} [SFinite μ0] [SFinite μ1]
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F.Carrier))
    {u0 : Langlands.GeneralLinear n0 F.Carrier → ℂ}
    {u1 : Langlands.GeneralLinear n1 F.Carrier → ℂ}
    (hu0m : AEStronglyMeasurable u0 μ0) (hu1m : AEStronglyMeasurable u1 μ1)
    (hu0 : ∀ Ψ : SchwartzBruhat (Matrix (Fin n0) (Fin n0) F.Carrier),
      Integrable (fun a => Ψ (GeneralLinear.inverseTranspose n0 F.Carrier a).val * u0 a) μ0)
    (hu1 : ∀ Ψ : SchwartzBruhat (Matrix (Fin n1) (Fin n1) F.Carrier),
      Integrable (fun d => Ψ (GeneralLinear.inverseTranspose n1 F.Carrier d).val *
        (u1 d * (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det : ℂ) ^ n0)) μ1)
    {ι : Type*} (S : Finset ι) (α : ι → SchwartzBruhat (Matrix (Fin n0) (Fin n0) F.Carrier))
    (β : ι → SchwartzBruhat (Matrix (Fin n1) (Fin n1) F.Carrier))
    (hpart : ∀ x y, ∫ C, Φ (blockMatrix e x 0 C y) ∂rectangularMeasure ν n1 n0 =
      ∑ k ∈ S, α k x * β k y) :
    Integrable (dualParabolicIntegrand F e Φ u0 u1)
        ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) ∧
      ∫ z, dualParabolicIntegrand F e Φ u0 u1 z
          ∂((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) =
        ∑ k ∈ S, (∫ a, α k (GeneralLinear.inverseTranspose n0 F.Carrier a).val * u0 a ∂μ0) *
          ∫ d, β k (GeneralLinear.inverseTranspose n1 F.Carrier d).val *
            (u1 d * (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det : ℂ) ^ n0)
            ∂μ1 := by
  obtain ⟨M, bA, bC, bD, hM⟩ := exists_blockMatrix_majorant e Φ
  let G : (Langlands.GeneralLinear n0 F.Carrier × Langlands.GeneralLinear n1 F.Carrier) →
      Matrix (Fin n1) (Fin n0) F.Carrier → ℂ := fun ad C =>
    Φ (blockMatrix e (GeneralLinear.inverseTranspose n0 F.Carrier ad.1).val 0 C
      (GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val)
  have hbC : Integrable (fun C => ‖bC C‖) (rectangularMeasure ν n1 n0) :=
    (bC.continuous.integrable_of_hasCompactSupport bC.hasCompactSupport).norm
  have hG : ∀ ad, Integrable (G ad) (rectangularMeasure ν n1 n0) := fun ad =>
    Integrable.mono' (hbC.const_mul (M * (‖bA (GeneralLinear.inverseTranspose n0 F.Carrier
        ad.1).val‖ * ‖bD (GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val‖)))
      (Φ.continuous.comp ((continuous_const.matrix_fromBlocks continuous_const continuous_id
        continuous_const).matrix_reindex e e)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun C => (hM _ C _).trans_eq (by ring))
  have hGnorm : ∀ ad, ∫ C, ‖G ad C‖ ∂rectangularMeasure ν n1 n0 ≤
      M * (‖bA (GeneralLinear.inverseTranspose n0 F.Carrier ad.1).val‖ *
        ‖bD (GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val‖) *
        ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0 := fun ad => by
    rw [← integral_const_mul]
    exact integral_mono (hG ad).norm (hbC.const_mul _) fun C => (hM _ C _).trans_eq (by ring)
  have hfib : ∀ ad x, dualParabolicIntegrand F e Φ u0 u1 (ad, x) =
      G ad (-((GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val * x.transpose)) *
        u0 ad.1 * u1 ad.2 := fun _ _ => rfl
  have hfibInt : ∀ ad, Integrable (fun x => dualParabolicIntegrand F e Φ u0 u1 (ad, x))
      (rectangularMeasure ν n0 n1) := fun ad => by
    simp only [hfib]
    exact ((integrable_comp_lowerLeft F ν ad.2 (hG ad)).mul_const _).mul_const _
  have hfibNorm : ∀ ad, ∫ x, ‖dualParabolicIntegrand F e Φ u0 u1 (ad, x)‖
      ∂rectangularMeasure ν n0 n1 =
        normalizedAbsoluteValue F.canonicalTopologicalData ad.2.val.det ^ n0 *
          (∫ C, ‖G ad C‖ ∂rectangularMeasure ν n1 n0) * ‖u0 ad.1‖ * ‖u1 ad.2‖ := fun ad => by
    simp only [hfib, norm_mul]
    rw [integral_mul_const, integral_mul_const,
      integral_comp_lowerLeft F ν ad.2 (fun C => ‖G ad C‖), smul_eq_mul]
  have hfibVal : ∀ ad, ∫ x, dualParabolicIntegrand F e Φ u0 u1 (ad, x)
      ∂rectangularMeasure ν n0 n1 =
        ∑ k ∈ S, (α k (GeneralLinear.inverseTranspose n0 F.Carrier ad.1).val * u0 ad.1) *
          (β k (GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val *
            (u1 ad.2 *
              (normalizedAbsoluteValue F.canonicalTopologicalData ad.2.val.det : ℂ) ^ n0)) :=
    fun ad => by
      simp only [hfib]
      rw [integral_mul_const, integral_mul_const, integral_comp_lowerLeft F ν ad.2 (G ad)]
      simp only [G, hpart, Complex.real_smul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
  have hQm := aestronglyMeasurable_dualParabolicIntegrand F e ν Φ hu0m hu1m
  have hint : Integrable (dualParabolicIntegrand F e Φ u0 u1)
      ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) := by
    rw [integrable_prod_iff hQm]
    refine ⟨Filter.Eventually.of_forall hfibInt, ?_⟩
    refine Integrable.mono'
      (((hu0 bA).norm.mul_prod (hu1 bD).norm).const_mul
        (M * ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0))
      hQm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ad => ?_)
    have h0 : 0 ≤ normalizedAbsoluteValue F.canonicalTopologicalData ad.2.val.det ^ n0 :=
      pow_nonneg (AbsoluteValue.nonneg _ _) n0
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hfibNorm]
    have h1 : 0 ≤ normalizedAbsoluteValue F.canonicalTopologicalData ad.2.val.det :=
      AbsoluteValue.nonneg _ _
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
    calc _ ≤ normalizedAbsoluteValue F.canonicalTopologicalData ad.2.val.det ^ n0 *
          (M * (‖bA (GeneralLinear.inverseTranspose n0 F.Carrier ad.1).val‖ *
            ‖bD (GeneralLinear.inverseTranspose n1 F.Carrier ad.2).val‖) *
            ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0) * ‖u0 ad.1‖ * ‖u1 ad.2‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hGnorm ad) h0) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  simp_rw [hfibVal]
  rw [integral_finsetSum _ fun k _ => (hu0 (α k)).mul_prod (hu1 (β k))]
  exact Finset.sum_congr rfl fun k _ => integral_prod_mul
    (fun a => α k (GeneralLinear.inverseTranspose n0 F.Carrier a).val * u0 a)
    (fun d => β k (GeneralLinear.inverseTranspose n1 F.Carrier d).val *
      (u1 d * (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det : ℂ) ^ n0))

end DualParabolic

section LeviCoordinates

variable {m : Fin 2 → ℕ} {N : ℕ} (e : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin N)

/-- **Dual parabolic reduction in Levi coordinates.** Let `g (L, x)` be the matrix
`[[L₀, L₀ x], [0, L₁]]` of the upper two-block parabolic, and integrate
`Φ ((g⁻¹)ᵀ) u₀(L₀) u₁(L₁)` against `(∏ᵢ μᵢ) × dx`. If the lower-left partial integral of
`Φ` is `∑ₖ αₖ(x) βₖ(y)`, the integrand is integrable and its integral is
`∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(m₀+1) dd)`. -/
theorem integrable_integral_dualParabolic_levi (ν : AdditiveHaarMeasure F.Carrier)
    (μ : ∀ i : Fin 2, Measure (Langlands.GeneralLinear (m i + 1) F.Carrier))
    [∀ i, SigmaFinite (μ i)]
    (g : (∀ i : Fin 2, Langlands.GeneralLinear (m i + 1) F.Carrier) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → Langlands.GeneralLinear N F.Carrier)
    (hg : ∀ L x, (g (L, x)).val =
      Matrix.reindex e e (Matrix.fromBlocks (L 0).val ((L 0).val * x) 0 (L 1).val))
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F.Carrier))
    {u0 : Langlands.GeneralLinear (m 0 + 1) F.Carrier → ℂ}
    {u1 : Langlands.GeneralLinear (m 1 + 1) F.Carrier → ℂ}
    (hu0m : AEStronglyMeasurable u0 (μ 0)) (hu1m : AEStronglyMeasurable u1 (μ 1))
    (hu0 : ∀ Ψ : SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier),
      Integrable (fun a => Ψ (GeneralLinear.inverseTranspose (m 0 + 1) F.Carrier a).val * u0 a)
        (μ 0))
    (hu1 : ∀ Ψ : SchwartzBruhat (Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier),
      Integrable (fun d => Ψ (GeneralLinear.inverseTranspose (m 1 + 1) F.Carrier d).val *
        (u1 d * (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det : ℂ) ^ (m 0 + 1)))
        (μ 1))
    {ι : Type*} (S : Finset ι)
    (α : ι → SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier))
    (β : ι → SchwartzBruhat (Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hpart : ∀ x y, ∫ C, Φ (blockMatrix e x 0 C y) ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1) =
      ∑ k ∈ S, α k x * β k y) :
    Integrable (fun z => Φ (GeneralLinear.inverseTranspose N F.Carrier (g z)).val *
        (u0 (z.1 0) * u1 (z.1 1)))
        ((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) ∧
      ∫ z, Φ (GeneralLinear.inverseTranspose N F.Carrier (g z)).val * (u0 (z.1 0) * u1 (z.1 1))
          ∂((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) =
        ∑ k ∈ S,
          (∫ a, α k (GeneralLinear.inverseTranspose (m 0 + 1) F.Carrier a).val * u0 a ∂μ 0) *
          ∫ d, β k (GeneralLinear.inverseTranspose (m 1 + 1) F.Carrier d).val *
            (u1 d * (normalizedAbsoluteValue F.canonicalTopologicalData d.val.det : ℂ) ^
              (m 0 + 1)) ∂μ 1 := by
  let Θ := (MeasurableEquiv.piFinTwo fun i : Fin 2 =>
      Langlands.GeneralLinear (m i + 1) F.Carrier).prodCongr
    (MeasurableEquiv.refl (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  have hΘ : MeasurePreserving Θ ((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1)))
      (((μ 0).prod (μ 1)).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) :=
    (measurePreserving_piFinTwo μ).prod (MeasurePreserving.id _)
  have hfun : (fun z => Φ (GeneralLinear.inverseTranspose N F.Carrier (g z)).val *
      (u0 (z.1 0) * u1 (z.1 1))) = dualParabolicIntegrand F e Φ u0 u1 ∘ Θ := by
    funext z
    obtain ⟨L, x⟩ := z
    change _ = Φ (blockMatrix e _ 0 _ _) * u0 (L 0) * u1 (L 1)
    rw [inverseTranspose_val_of_upperBlock e (g (L, x)) (L 0) (L 1) x (hg L x), mul_assoc]
    rfl
  obtain ⟨hint, hval⟩ := integrable_integral_dualParabolicIntegrand F e ν Φ hu0m hu1m hu0 hu1
    S α β hpart
  rw [hfun]
  exact ⟨(hΘ.integrable_comp_emb Θ.measurableEmbedding).mpr hint,
    (hΘ.integral_comp' (dualParabolicIntegrand F e Φ u0 u1)).trans hval⟩

end LeviCoordinates

section CompactTranslate

/-- **Dual compact step.** If the two-sided translate `x ↦ Φ (A x B)` by matrices of
normalized determinant one decomposes as `∑ₗ cₗ Φₗ`, then the Fourier transform of `Φ` at
the inverse transpose of `A g B` decomposes with the same coefficients as
`∑ₗ cₗ (FΦₗ)((g⁻¹)ᵀ)`. -/
theorem rectangularFourierEquiv_inverseTranspose_translate
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {n : ℕ} (A B : Langlands.GeneralLinear n F.Carrier)
    (hA : F.canonicalTopologicalData.determinantNorm n A = 1)
    (hB : F.canonicalTopologicalData.determinantNorm n B = 1)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) F.Carrier)) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (Φs : ι → SchwartzBruhat (Matrix (Fin n) (Fin n) F.Carrier))
    (hdec : ∀ x, Φ (A.val * x * B.val) = ∑ l ∈ S, c l * Φs l x)
    (g : Langlands.GeneralLinear n F.Carrier) :
    rectangularFourierEquiv ψ ν n n hsd Φ
        (GeneralLinear.inverseTranspose n F.Carrier (A * (g * B))).val =
      ∑ l ∈ S, c l * rectangularFourierEquiv ψ ν n n hsd (Φs l)
        (GeneralLinear.inverseTranspose n F.Carrier g).val := by
  rw [← mul_assoc, map_mul, map_mul, Units.val_mul, Units.val_mul]
  simp only [rectangularFourierEquiv_apply]
  exact rectangularFourierIntegral_translate_decomposition F.canonicalTopologicalData ψ ν A B
    hA hB Φ S c Φs hdec _

/-- The dual compact step for two elements of a compact subgroup of `GL_n`. -/
theorem rectangularFourierEquiv_inverseTranspose_translate_of_mem
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {n : ℕ} (K : Subgroup (Langlands.GeneralLinear n F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear n F.Carrier)))
    {A B : Langlands.GeneralLinear n F.Carrier} (hA : A ∈ K) (hB : B ∈ K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) F.Carrier)) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (Φs : ι → SchwartzBruhat (Matrix (Fin n) (Fin n) F.Carrier))
    (hdec : ∀ x, Φ (A.val * x * B.val) = ∑ l ∈ S, c l * Φs l x)
    (g : Langlands.GeneralLinear n F.Carrier) :
    rectangularFourierEquiv ψ ν n n hsd Φ
        (GeneralLinear.inverseTranspose n F.Carrier (A * (g * B))).val =
      ∑ l ∈ S, c l * rectangularFourierEquiv ψ ν n n hsd (Φs l)
        (GeneralLinear.inverseTranspose n F.Carrier g).val :=
  rectangularFourierEquiv_inverseTranspose_translate F ψ ν hsd A B
    (F.canonicalTopologicalData.determinantNorm_eq_one_of_mem_compact n K hK A hA)
    (F.canonicalTopologicalData.determinantNorm_eq_one_of_mem_compact n K hK B hB) Φ S c Φs hdec g

end CompactTranslate

end Padic

end Langlands.GodementJacquet
