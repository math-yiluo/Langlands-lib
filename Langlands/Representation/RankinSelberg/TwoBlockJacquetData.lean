import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.Shahidi.Characters
import Langlands.Representation.Shahidi.LocalCoefficientPadic
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Two-block scalar sections and absolute Jacquet integral data

JPSS 1983, Section 4.6, printed pages 410-411: for representations `σ_1, σ_2` of
`GL_(m_1+1)(F)` and `GL_(m_2+1)(F)` with `(m_1+1) + (m_2+1) = t+1`, the sections
of the normalized induction from the lower block parabolic satisfy the
covariance (4.6.1), and the integrand of (4.6.2) is a scalar evaluation of a
section at `u g`, for `u` in the complementary upper radical, against the
positive character of the upper-right corner entry of `u`.

This module defines that data for the published actual lower induction
`F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)` with
`B = succBlockShape m h`: scalar evaluation through supplied linear functionals
on the block carriers, the upper radical matrix, the positive kernel, the raw
integrand, its Bochner integral against a supplied measure and the absolute
integrability conditions. It asserts no convergence.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockJacquet

open GeneralLinear

universe uι uF uW uR

section Contraction

variable {ι : Type uι} [Fintype ι] {W : ι → Type uW}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Contraction of `⨂_i W_i` against functionals `ℓ_i`: the linear map induced by
the multilinear map `v ↦ ∏_i ℓ_i (v_i)`. -/
def tensorContraction (ell : ∀ i, W i →ₗ[ℂ] ℂ) : PiTensorProduct ℂ W →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ell)

@[simp]
theorem tensorContraction_tprod (ell : ∀ i, W i →ₗ[ℂ] ℂ) (v : ∀ i, W i) :
    tensorContraction ell (PiTensorProduct.tprod ℂ v) = ∏ i, ell i (v i) := by
  rw [tensorContraction, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]

end Contraction

/-- On the two-factor carrier `pairCarrier V₁ V₂`, the contraction against
`pairFactorFunctional ℓ₁ ℓ₂` is Shahidi's `pairFunctional ℓ₁ ℓ₂`. -/
theorem tensorContraction_pairFactorFunctional {V₁ V₂ : Type uW}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    tensorContraction (Shahidi.pairFactorFunctional ℓ₁ ℓ₂) = Shahidi.pairFunctional ℓ₁ ℓ₂ :=
  rfl

section Radical

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The two block ranks add up to the total rank. -/
theorem blockRanks_add (h : ∑ i, (m i + 1) = t + 1) : m 0 + 1 + (m 1 + 1) = t + 1 := by
  simpa only [Fin.sum_univ_two] using h

/-- The coordinates of the first block are the first `m 0 + 1` coordinates. -/
theorem index_zero (i : Fin (m 0 + 1)) :
    (succBlockShape m h).index 0 i = Fin.cast (blockRanks_add h) (i.castAdd (m 1 + 1)) := by
  apply Fin.ext
  simp only [BlockShape.index, BlockShape.indexEquiv, Function.Embedding.coeFn_mk,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp

/-- The coordinates of the second block are the last `m 1 + 1` coordinates. -/
theorem index_one (j : Fin (m 1 + 1)) :
    (succBlockShape m h).index 1 j = Fin.cast (blockRanks_add h) (j.natAdd (m 0 + 1)) := by
  apply Fin.ext
  simp only [BlockShape.index, BlockShape.indexEquiv, Function.Embedding.coeFn_mk,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp only [Fin.val_natAdd]
  rfl

variable (R : Type uR) [CommRing R]

/-- The complementary upper radical matrix `[[I, x], [0, I]]` of `GL_(t+1)`: Shahidi's
`upper` matrix, transported along `(m 0 + 1) + (m 1 + 1) = t + 1`. -/
def upperRadical (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    GeneralLinear (t + 1) R :=
  GeneralLinear.reindex (finCongr (blockRanks_add h))
    (Shahidi.upper (m 0 + 1) (m 1 + 1) R x)

theorem upperRadical_apply_cast (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (i j : Fin (m 0 + 1 + (m 1 + 1))) :
    upperRadical h R x (Fin.cast (blockRanks_add h) i) (Fin.cast (blockRanks_add h) j) =
      Shahidi.upper (m 0 + 1) (m 1 + 1) R x i j :=
  rfl

@[simp]
theorem upperRadical_zero : upperRadical h R 0 = 1 := by
  rw [upperRadical, Shahidi.upper_zero, map_one]

theorem upperRadical_add (x y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperRadical h R (x + y) = upperRadical h R x * upperRadical h R y := by
  rw [upperRadical, Shahidi.upper_add, map_mul]
  rfl

@[simp]
theorem upperRadical_neg (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperRadical h R (-x) = (upperRadical h R x)⁻¹ := by
  rw [upperRadical, Shahidi.upper_neg, map_inv]
  rfl

theorem upperRadical_sub (x y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperRadical h R (x - y) = upperRadical h R x * (upperRadical h R y)⁻¹ := by
  rw [sub_eq_add_neg, upperRadical_add, upperRadical_neg]

/-- The upper-right rectangle of `upperRadical h R x`, in block coordinates, is `x`. -/
@[simp]
theorem upperRadical_index_zero_one (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (i : Fin (m 0 + 1)) (j : Fin (m 1 + 1)) :
    upperRadical h R x ((succBlockShape m h).index 0 i) ((succBlockShape m h).index 1 j) =
      x i j := by
  rw [index_zero, index_one, upperRadical_apply_cast, Shahidi.upper_first_second]

@[simp]
theorem upperRadical_index_zero_zero (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (i j : Fin (m 0 + 1)) :
    upperRadical h R x ((succBlockShape m h).index 0 i) ((succBlockShape m h).index 0 j) =
      if i = j then 1 else 0 := by
  rw [index_zero, index_zero, upperRadical_apply_cast, Shahidi.upper_first_first]

@[simp]
theorem upperRadical_index_one_zero (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (i : Fin (m 1 + 1)) (j : Fin (m 0 + 1)) :
    upperRadical h R x ((succBlockShape m h).index 1 i) ((succBlockShape m h).index 0 j) =
      0 := by
  rw [index_one, index_zero, upperRadical_apply_cast, Shahidi.upper_second_first]

@[simp]
theorem upperRadical_index_one_one (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R)
    (i j : Fin (m 1 + 1)) :
    upperRadical h R x ((succBlockShape m h).index 1 i) ((succBlockShape m h).index 1 j) =
      if i = j then 1 else 0 := by
  rw [index_one, index_one, upperRadical_apply_cast, Shahidi.upper_second_second]

theorem upperRadical_injective : Function.Injective (upperRadical (m := m) h R) := by
  intro x y hxy
  ext i j
  rw [← upperRadical_index_zero_one h R x i j, ← upperRadical_index_zero_one h R y i j, hxy]

theorem continuous_upperRadical [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (upperRadical (m := m) h R) :=
  (GeneralLinear.reindexContinuous (R := R) (finCongr (blockRanks_add h))).continuous.comp
    (Shahidi.continuous_upper (m 0 + 1) (m 1 + 1) R)

end Radical

section Kernel

variable {R : Type uR} [CommRing R]

/-- The sum of the superdiagonal entries of Shahidi's upper matrix is the corner
entry `x_(last,0)`. -/
theorem sum_superdiagonal_upper {a b : ℕ} (x : Matrix (Fin (a + 1)) (Fin (b + 1)) R) :
    ∑ i : Fin (a + 1 + b), Shahidi.upper (a + 1) (b + 1) R x i.castSucc i.succ =
      x (Fin.last a) 0 := by
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  have h₁ : ∀ j : Fin a, Shahidi.upper (a + 1) (b + 1) R x
      (Fin.castAdd b j.castSucc).castSucc (Fin.castAdd b j.castSucc).succ = 0 := by
    intro j
    have e₁ : ((Fin.castAdd b j.castSucc).castSucc : Fin (a + 1 + (b + 1))) =
        Fin.castAdd (b + 1) j.castSucc := Fin.ext (by simp)
    have e₂ : ((Fin.castAdd b j.castSucc).succ : Fin (a + 1 + (b + 1))) =
        Fin.castAdd (b + 1) j.succ := Fin.ext (by simp)
    rw [e₁, e₂, Shahidi.upper_first_first, ite_eq_right_iff]
    intro hj
    simpa using congrArg Fin.val hj
  have h₂ : ∀ j : Fin b, Shahidi.upper (a + 1) (b + 1) R x
      (Fin.natAdd (a + 1) j).castSucc (Fin.natAdd (a + 1) j).succ = 0 := by
    intro j
    have e₁ : ((Fin.natAdd (a + 1) j).castSucc : Fin (a + 1 + (b + 1))) =
        Fin.natAdd (a + 1) j.castSucc := Fin.ext (by simp)
    have e₂ : ((Fin.natAdd (a + 1) j).succ : Fin (a + 1 + (b + 1))) =
        Fin.natAdd (a + 1) j.succ := Fin.ext (by simp; omega)
    rw [e₁, e₂, Shahidi.upper_second_second, ite_eq_right_iff]
    intro hj
    simpa using congrArg Fin.val hj
  have e₁ : ((Fin.castAdd b (Fin.last a)).castSucc : Fin (a + 1 + (b + 1))) =
      Fin.castAdd (b + 1) (Fin.last a) := Fin.ext (by simp)
  have e₂ : ((Fin.castAdd b (Fin.last a)).succ : Fin (a + 1 + (b + 1))) =
      (Fin.natAdd (a + 1) (0 : Fin (b + 1)) : Fin (a + 1 + (b + 1))) := Fin.ext (by simp)
  rw [Finset.sum_eq_zero (fun j _ => h₁ j), Finset.sum_eq_zero (fun j _ => h₂ j), e₁, e₂,
    Shahidi.upper_first_second, zero_add, add_zero]

variable [TopologicalSpace R] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter R)
variable {m : Fin 2 → ℕ}

/-- The scalar kernel of JPSS (4.6.2): the positive character `ψ` of the upper
radical, `Shahidi.upperCharacter` before the total-rank reindexing. -/
def positiveKernel (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) : ℂ :=
  (Shahidi.upperCharacter (m 0) (m 1) ψ (Multiplicative.ofAdd x) : ℂ)

/-- The kernel is the positive character `ψ` of the corner entry `x_(m 0, 0)`. -/
theorem positiveKernel_apply (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    positiveKernel ψ x = ψ.complex (x (Fin.last (m 0)) 0) := by
  rw [positiveKernel, Shahidi.upperCharacter_apply, sum_superdiagonal_upper]

/-- The kernel is the positive standard character `ψ(∑_i u_(i,i+1))` of the total-rank
upper radical matrix `u = upperRadical h R x`. -/
theorem positiveKernel_eq_superdiagonal_upperRadical {t : ℕ} (h : ∑ i, (m i + 1) = t + 1)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    positiveKernel ψ x = ψ.complex (∑ i : Fin t, upperRadical h R x i.castSucc i.succ) := by
  obtain rfl : t = m 0 + 1 + m 1 := by
    have := blockRanks_add h
    omega
  rfl

@[simp]
theorem norm_positiveKernel (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    ‖positiveKernel ψ x‖ = 1 :=
  Shahidi.norm_upperCharacter (m 0) (m 1) ψ x

@[simp]
theorem positiveKernel_zero : positiveKernel (m := m) ψ 0 = 1 := by
  rw [positiveKernel_apply, Matrix.zero_apply, AddChar.map_zero_eq_one]

theorem positiveKernel_add (x y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    positiveKernel ψ (x + y) = positiveKernel ψ x * positiveKernel ψ y := by
  rw [positiveKernel_apply, positiveKernel_apply, positiveKernel_apply, Matrix.add_apply,
    AddChar.map_add_eq_mul]

/-- Shahidi's `upperJacquetKernel` uses the conjugate character: the positive kernel
is its inverse. -/
theorem positiveKernel_eq_inv_upperJacquetKernel
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    positiveKernel ψ x = (Shahidi.upperJacquetKernel (m 0) (m 1) ψ x)⁻¹ := by
  rw [Shahidi.upperJacquetKernel_eq_inv, inv_inv, positiveKernel]

/-- The positive kernel is the complex conjugate of Shahidi's `upperJacquetKernel`. -/
theorem positiveKernel_eq_conj_upperJacquetKernel
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    positiveKernel ψ x = starRingEnd ℂ (Shahidi.upperJacquetKernel (m 0) (m 1) ψ x) := by
  rw [Shahidi.upperJacquetKernel, Complex.conj_conj, positiveKernel]

theorem continuous_positiveKernel [IsTopologicalRing R] :
    Continuous (positiveKernel (m := m) ψ) := by
  have h := (Shahidi.continuous_upperJacquetKernel (m 0) (m 1) ψ).star
  refine h.congr fun x => ?_
  rw [positiveKernel_eq_conj_upperJacquetKernel]
  rfl

end Kernel

section Sections

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- The carrier of the actual lower induction
`F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)`,
`B = succBlockShape m h`: the sections of JPSS (4.6.1). -/
abbrev Sections : Type (max uF uW) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  Induction.SmoothFunctions ((succBlockShape m h).oppositeParabolic F.Carrier)
    (twist (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp
        ((succBlockShape m h).oppositeLeviProjection F.Carrier)))

/-- The actual lower induced representation `I(σ_1 ⊗ σ_2)`, acting on `Sections`. -/
abbrev inducedRep :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    Representation ℂ (GeneralLinear (t + 1) F.Carrier) (Sections F h σ) :=
  F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
    ((succBlockShape m h).blockTensor σ)

/-- Evaluation of a section at an ambient element. -/
abbrev sectionEval (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    PiTensorProduct ℂ W :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  Induction.eval ((succBlockShape m h).oppositeParabolic F.Carrier)
    (twist (F.canonicalTopologicalData.oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp
        ((succBlockShape m h).oppositeLeviProjection F.Carrier))) f g

variable {F h σ}

/-- The scalar section `(g, a) ↦ (⊗ ℓ_i) ((σ_1 ⊗ σ_2)(a) f(g))` at an ambient element `g`
and an actual block Levi element `a`. -/
def scalarSection (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) : ℂ :=
  tensorContraction ell ((succBlockShape m h).blockTensor σ a (sectionEval F h σ f g))

theorem scalarSection_def (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    scalarSection ell f g a =
      tensorContraction ell ((succBlockShape m h).blockTensor σ a (sectionEval F h σ f g)) :=
  rfl

@[simp]
theorem scalarSection_one (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    scalarSection ell f g 1 = tensorContraction ell (sectionEval F h σ f g) := by
  rw [scalarSection_def, map_one, Module.End.one_apply]

/-- Evaluation on a section whose value at `g` is the pure tensor `⊗ v_i`. -/
theorem scalarSection_of_eval_eq_tprod (ell : ∀ i, W i →ₗ[ℂ] ℂ) {f : Sections F h σ}
    {g : GeneralLinear (t + 1) F.Carrier} {v : ∀ i, W i}
    (hv : sectionEval F h σ f g = PiTensorProduct.tprod ℂ v)
    (a : (succBlockShape m h).Levi F.Carrier) :
    scalarSection ell f g a = ∏ i, ell i (σ i (a i) (v i)) := by
  rw [scalarSection_def, hv, BlockShape.blockTensor_tprod, tensorContraction_tprod]

@[simp]
theorem sectionEval_add (f f' : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ (f + f') g = sectionEval F h σ f g + sectionEval F h σ f' g :=
  rfl

@[simp]
theorem sectionEval_smul (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ (c • f) g = c • sectionEval F h σ f g :=
  rfl

@[simp]
theorem sectionEval_zero (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    sectionEval F h σ 0 g = 0 :=
  rfl

@[simp]
theorem scalarSection_add (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f f' : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    scalarSection ell (f + f') g a = scalarSection ell f g a + scalarSection ell f' g a := by
  simp only [scalarSection_def, sectionEval_add, map_add]

@[simp]
theorem scalarSection_smul (ell : ∀ i, W i →ₗ[ℂ] ℂ) (c : ℂ) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    scalarSection ell (c • f) g a = c * scalarSection ell f g a := by
  simp only [scalarSection_def, sectionEval_smul, map_smul, smul_eq_mul]

@[simp]
theorem scalarSection_zero (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    scalarSection ell (0 : Sections F h σ) g a = 0 := by
  simp only [scalarSection_def, sectionEval_zero, map_zero]

/-- The scalar section at a fixed `(g, a)` as a linear functional of the section. -/
def scalarSectionMap (ell : ∀ i, W i →ₗ[ℂ] ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (a : (succBlockShape m h).Levi F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    Sections F h σ →ₗ[ℂ] ℂ :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  { toFun := fun f => scalarSection ell f g a
    map_add' := fun f f' => scalarSection_add ell f f' g a
    map_smul' := fun c f => scalarSection_smul ell c f g a }

@[simp]
theorem scalarSectionMap_apply (ell : ∀ i, W i →ₗ[ℂ] ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (a : (succBlockShape m h).Levi F.Carrier) (f : Sections F h σ) :
    scalarSectionMap ell g a f = scalarSection ell f g a :=
  rfl

/-- Compatibility with the actual induced right translation. -/
@[simp]
theorem scalarSection_inducedRep (ell : ∀ i, W i →ₗ[ℂ] ℂ)
    (g' : GeneralLinear (t + 1) F.Carrier) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    scalarSection ell (inducedRep F h σ g' f) g a = scalarSection ell f (g * g') a :=
  rfl

/-- The covariance (4.6.1) of scalar sections: if the lower parabolic element `q`
has Levi projection `b`, then the value at `(q g, a)` is `δ_P(b)^(-1/2)` times the
value at `(g, a b)`, for the upper block modulus `δ_P`. -/
theorem scalarSection_covariant (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h σ)
    (q : (succBlockShape m h).oppositeParabolic F.Carrier)
    {b : (succBlockShape m h).Levi F.Carrier}
    (hq : (succBlockShape m h).oppositeLeviProjection F.Carrier q = b)
    (g : GeneralLinear (t + 1) F.Carrier) (a : (succBlockShape m h).Levi F.Carrier) :
    scalarSection ell f ((q : GeneralLinear (t + 1) F.Carrier) * g) a =
      ((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹ *
        scalarSection ell f g (a * b) := by
  subst hq
  rw [scalarSection_def, sectionEval,
    F.canonicalTopologicalData.normalizedOppositeParabolicInduced_covariant, map_smul,
    map_smul, scalarSection_def, map_mul, Module.End.mul_apply,
    PadicField.TopologicalData.leviHalfModulus_apply, smul_eq_mul]

end Sections

section Integral

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable (ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- The raw scalar integrand of JPSS (4.6.2):
`x ↦ ⟨f(u(x) g), ⊗ ℓ_i⟩ ψ(x_(m 0, 0))`. -/
def integrand (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  scalarSection ell f (upperRadical h F.Carrier x * g) 1 * positiveKernel ψ x

theorem integrand_def (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    integrand ψ ell f g x =
      letI := F.canonicalTopologicalData.topology
      scalarSection ell f (upperRadical h F.Carrier x * g) 1 * positiveKernel ψ x :=
  rfl

/-- The integrand with the kernel evaluated at the corner entry. -/
theorem integrand_apply (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    integrand ψ ell f g x =
      letI := F.canonicalTopologicalData.topology
      tensorContraction ell (sectionEval F h σ f (upperRadical h F.Carrier x * g)) *
        ψ.complex (x (Fin.last (m 0)) 0) := by
  let := F.canonicalTopologicalData.topology
  rw [integrand_def, scalarSection_one, positiveKernel_apply]

@[simp]
theorem integrand_add (f f' : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    integrand ψ ell (f + f') g x = integrand ψ ell f g x + integrand ψ ell f' g x := by
  simp only [integrand_def, scalarSection_add, add_mul]

@[simp]
theorem integrand_smul (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    integrand ψ ell (c • f) g x = c * integrand ψ ell f g x := by
  simp only [integrand_def, scalarSection_smul, mul_assoc]

@[simp]
theorem integrand_zero (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    integrand ψ ell (0 : Sections F h σ) g x = 0 := by
  simp only [integrand_def, scalarSection_zero, zero_mul]

/-- Raw right translation: translating the section by `g'` translates the integrand's
ambient argument. -/
@[simp]
theorem integrand_inducedRep (g' : GeneralLinear (t + 1) F.Carrier) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ψ ell (inducedRep F h σ g' f) g = integrand ψ ell f (g * g') := by
  funext x
  rw [integrand_def, integrand_def, scalarSection_inducedRep, mul_assoc]

variable [MeasurableSpace F.Carrier]
variable (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))

/-- The function `g ↦ ∫ ⟨f(u g), ⊗ ℓ_i⟩ ψ(u) du` of JPSS (4.6.2), as the ordinary
Bochner integral against the supplied measure `μ` on the rectangular coordinates. -/
def jacquetFunction (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ x, integrand ψ ell f g x ∂μ

theorem jacquetFunction_def (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    jacquetFunction ψ ell μ f g = ∫ x, integrand ψ ell f g x ∂μ :=
  rfl

/-- The integral written out with the corner kernel. -/
theorem jacquetFunction_apply (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    jacquetFunction ψ ell μ f g =
      letI := F.canonicalTopologicalData.topology
      ∫ x, tensorContraction ell (sectionEval F h σ f (upperRadical h F.Carrier x * g)) *
        ψ.complex (x (Fin.last (m 0)) 0) ∂μ := by
  rw [jacquetFunction_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (integrand_apply ψ ell f g))

/-- Absolute integrability of the integrand at `g`. -/
def IsAbsIntegrableAt (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) : Prop :=
  Integrable (integrand ψ ell f g) μ

/-- Absolute integrability of the integrand at every `g`. -/
def IsAbsIntegrable (f : Sections F h σ) : Prop :=
  ∀ g, IsAbsIntegrableAt ψ ell μ f g

theorem isAbsIntegrableAt_zero (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrableAt ψ ell μ (0 : Sections F h σ) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  unfold IsAbsIntegrableAt
  rw [show integrand ψ ell (0 : Sections F h σ) g = 0 from funext (integrand_zero ψ ell g)]
  exact integrable_zero _ _ _

theorem IsAbsIntegrableAt.add {f f' : Sections F h σ} {g : GeneralLinear (t + 1) F.Carrier}
    (hf : IsAbsIntegrableAt ψ ell μ f g) (hf' : IsAbsIntegrableAt ψ ell μ f' g) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrableAt ψ ell μ (f + f') g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  unfold IsAbsIntegrableAt at *
  rw [show integrand ψ ell (f + f') g = integrand ψ ell f g + integrand ψ ell f' g from
    funext (integrand_add ψ ell f f' g)]
  exact hf.add hf'

theorem IsAbsIntegrableAt.smul {f : Sections F h σ} {g : GeneralLinear (t + 1) F.Carrier}
    (hf : IsAbsIntegrableAt ψ ell μ f g) (c : ℂ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrableAt ψ ell μ (c • f) g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  unfold IsAbsIntegrableAt at *
  rw [show integrand ψ ell (c • f) g = fun x => c * integrand ψ ell f g x from
    funext (integrand_smul ψ ell c f g)]
  exact hf.const_mul c

theorem isAbsIntegrable_zero :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrable ψ ell μ (0 : Sections F h σ) :=
  fun g => isAbsIntegrableAt_zero ψ ell μ g

theorem IsAbsIntegrable.add {f f' : Sections F h σ}
    (hf : IsAbsIntegrable ψ ell μ f) (hf' : IsAbsIntegrable ψ ell μ f') :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrable ψ ell μ (f + f') :=
  fun g => (hf g).add ψ ell μ (hf' g)

theorem IsAbsIntegrable.smul {f : Sections F h σ} (hf : IsAbsIntegrable ψ ell μ f) (c : ℂ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    IsAbsIntegrable ψ ell μ (c • f) :=
  fun g => (hf g).smul ψ ell μ c

/-- Additivity of the integral under absolute integrability of both integrands. -/
theorem jacquetFunction_add {f f' : Sections F h σ} {g : GeneralLinear (t + 1) F.Carrier}
    (hf : IsAbsIntegrableAt ψ ell μ f g) (hf' : IsAbsIntegrableAt ψ ell μ f' g) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    jacquetFunction ψ ell μ (f + f') g = jacquetFunction ψ ell μ f g + jacquetFunction ψ ell μ f' g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  simp only [jacquetFunction_def, integrand_add]
  exact integral_add hf hf'

/-- Complex homogeneity of the integral. -/
theorem jacquetFunction_smul (c : ℂ) (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    jacquetFunction ψ ell μ (c • f) g = c * jacquetFunction ψ ell μ f g := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  simp only [jacquetFunction_def, integrand_smul]
  exact integral_const_mul c _

@[simp]
theorem jacquetFunction_zero (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    jacquetFunction ψ ell μ (0 : Sections F h σ) g = 0 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  simp only [jacquetFunction_def, integrand_zero, integral_zero]

/-- Raw right translation of absolute integrability. -/
theorem isAbsIntegrableAt_inducedRep_iff (g' : GeneralLinear (t + 1) F.Carrier)
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    IsAbsIntegrableAt ψ ell μ (inducedRep F h σ g' f) g ↔
      IsAbsIntegrableAt ψ ell μ f (g * g') := by
  rw [IsAbsIntegrableAt, IsAbsIntegrableAt, integrand_inducedRep]

theorem IsAbsIntegrable.inducedRep {f : Sections F h σ} (hf : IsAbsIntegrable ψ ell μ f)
    (g' : GeneralLinear (t + 1) F.Carrier) :
    IsAbsIntegrable ψ ell μ (TwoBlockJacquet.inducedRep F h σ g' f) :=
  fun g => (isAbsIntegrableAt_inducedRep_iff ψ ell μ g' f g).mpr (hf (g * g'))

/-- Raw right translation of the integral. -/
@[simp]
theorem jacquetFunction_inducedRep (g' : GeneralLinear (t + 1) F.Carrier) (f : Sections F h σ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    jacquetFunction ψ ell μ (inducedRep F h σ g' f) g = jacquetFunction ψ ell μ f (g * g') := by
  rw [jacquetFunction_def, jacquetFunction_def, integrand_inducedRep]

end Integral

end Langlands.RankinSelberg.TwoBlockJacquet
