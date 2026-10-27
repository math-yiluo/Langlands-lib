import Langlands.Group.GL.Basic
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Actual affine equivalences of column vectors and additive Haar pushforward

The affine map `x ↦ A.val.mulVec x + v` on `Fin n → R`, packaged as an
equivalence, a homeomorphism and a measurable equivalence, with its additive
Haar change-of-variables laws. See the paired Markdown for hypotheses,
conventions and provenance.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix
open scoped NNReal

namespace Langlands.AffineChangeOfVariables

universe u

section Algebra

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The actual column-vector affine map, with its matrix inverse. -/
def equiv (A : GeneralLinear n R) (v : Fin n → R) :
    (Fin n → R) ≃ (Fin n → R) where
  toFun x := A.val.mulVec x + v
  invFun x := (A⁻¹).val.mulVec (x - v)
  left_inv x := by
    change (A⁻¹).val.mulVec ((A.val.mulVec x + v) - v) = x
    rw [add_sub_cancel_right, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv x := by
    change A.val.mulVec ((A⁻¹).val.mulVec (x - v)) + v = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, sub_add_cancel]

@[simp] theorem equiv_apply (A : GeneralLinear n R) (v x : Fin n → R) :
    equiv A v x = A.val.mulVec x + v := rfl

@[simp] theorem equiv_symm_apply (A : GeneralLinear n R) (v x : Fin n → R) :
    (equiv A v).symm x = (A⁻¹).val.mulVec (x - v) := rfl

theorem equiv_symm (A : GeneralLinear n R) (v : Fin n → R) :
    (equiv A v).symm = equiv A⁻¹ (-((A⁻¹).val.mulVec v)) := by
  apply Equiv.ext
  intro x
  change (A⁻¹).val.mulVec (x - v) =
    (A⁻¹).val.mulVec x + -((A⁻¹).val.mulVec v)
  rw [Matrix.mulVec_sub, sub_eq_add_neg]

@[simp] theorem equiv_one_zero :
    equiv (1 : GeneralLinear n R) 0 = Equiv.refl (Fin n → R) := by
  apply Equiv.ext
  intro x
  simp [equiv]

/-- The later affine map is the left matrix factor. -/
theorem equiv_trans (A B : GeneralLinear n R) (v w : Fin n → R) :
    (equiv B w).trans (equiv A v) =
      equiv (A * B) (v + A.val.mulVec w) := by
  apply Equiv.ext
  intro x
  change A.val.mulVec (B.val.mulVec x + w) + v =
    (A.val * B.val).mulVec x + (v + A.val.mulVec w)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  simp only [add_comm, add_left_comm]

/-- The composition law as functions: `S(A,v) ∘ S(B,w) = S(AB, v + A.val.mulVec w)`. -/
theorem equiv_comp (A B : GeneralLinear n R) (v w : Fin n → R) :
    ⇑(equiv A v) ∘ ⇑(equiv B w) = ⇑(equiv (A * B) (v + A.val.mulVec w)) :=
  congrArg DFunLike.coe (equiv_trans A B v w)

end Algebra

section Topology

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] {n : ℕ}

/-- The affine equivalence in the inherited finite product topology. -/
def homeomorph (A : GeneralLinear n R) (v : Fin n → R) :
    (Fin n → R) ≃ₜ (Fin n → R) where
  toEquiv := equiv A v
  continuous_toFun := (continuous_const.matrix_mulVec continuous_id).add continuous_const
  continuous_invFun :=
    continuous_const.matrix_mulVec (continuous_id.sub continuous_const)

@[simp] theorem homeomorph_apply (A : GeneralLinear n R) (v x : Fin n → R) :
    homeomorph A v x = A.val.mulVec x + v := rfl

@[simp] theorem homeomorph_symm_apply (A : GeneralLinear n R) (v x : Fin n → R) :
    (homeomorph A v).symm x = (A⁻¹).val.mulVec (x - v) := rfl

theorem homeomorph_toEquiv (A : GeneralLinear n R) (v : Fin n → R) :
    (homeomorph A v).toEquiv = equiv A v := rfl

theorem homeomorph_symm (A : GeneralLinear n R) (v : Fin n → R) :
    (homeomorph A v).symm = homeomorph A⁻¹ (-((A⁻¹).val.mulVec v)) := by
  apply Homeomorph.ext
  intro x
  exact congrArg (fun e : (Fin n → R) ≃ (Fin n → R) => e x) (equiv_symm A v)

@[simp] theorem homeomorph_one_zero :
    homeomorph (1 : GeneralLinear n R) 0 = Homeomorph.refl (Fin n → R) := by
  apply Homeomorph.ext
  intro x
  simp

theorem homeomorph_trans (A B : GeneralLinear n R) (v w : Fin n → R) :
    (homeomorph B w).trans (homeomorph A v) =
      homeomorph (A * B) (v + A.val.mulVec w) := by
  apply Homeomorph.ext
  intro x
  exact congrArg (fun e : (Fin n → R) ≃ (Fin n → R) => e x) (equiv_trans A B v w)

variable [MeasurableSpace (Fin n → R)] [BorelSpace (Fin n → R)]

/-- The same actual affine map for any Borel measurable structure on the vectors. -/
def measurableEquiv (A : GeneralLinear n R) (v : Fin n → R) :
    (Fin n → R) ≃ᵐ (Fin n → R) :=
  (homeomorph A v).toMeasurableEquiv

@[simp] theorem measurableEquiv_apply
    (A : GeneralLinear n R) (v x : Fin n → R) :
    measurableEquiv A v x = A.val.mulVec x + v := rfl

@[simp] theorem measurableEquiv_symm_apply
    (A : GeneralLinear n R) (v x : Fin n → R) :
    (measurableEquiv A v).symm x = (A⁻¹).val.mulVec (x - v) := rfl

theorem measurableEquiv_toEquiv (A : GeneralLinear n R) (v : Fin n → R) :
    (measurableEquiv A v).toEquiv = equiv A v := rfl

theorem measurableEquiv_symm (A : GeneralLinear n R) (v : Fin n → R) :
    (measurableEquiv A v).symm =
      measurableEquiv A⁻¹ (-((A⁻¹).val.mulVec v)) := by
  apply MeasurableEquiv.ext
  funext x
  exact congrArg (fun e : (Fin n → R) ≃ (Fin n → R) => e x) (equiv_symm A v)

@[simp] theorem measurableEquiv_one_zero :
    measurableEquiv (1 : GeneralLinear n R) 0 =
      MeasurableEquiv.refl (Fin n → R) := by
  apply MeasurableEquiv.ext
  funext x
  simp

theorem measurableEquiv_trans (A B : GeneralLinear n R) (v w : Fin n → R) :
    (measurableEquiv B w).trans (measurableEquiv A v) =
      measurableEquiv (A * B) (v + A.val.mulVec w) := by
  apply MeasurableEquiv.ext
  funext x
  exact congrArg (fun e : (Fin n → R) ≃ (Fin n → R) => e x) (equiv_trans A B v w)

/-- The measurable composition law as functions, in the order `S(A,v) ∘ S(B,w)`. -/
theorem measurableEquiv_comp (A B : GeneralLinear n R) (v w : Fin n → R) :
    ⇑(measurableEquiv A v) ∘ ⇑(measurableEquiv B w) =
      ⇑(measurableEquiv (A * B) (v + A.val.mulVec w)) :=
  equiv_comp A B v w

end Topology

section Haar

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K] {n : ℕ}
  [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]

/-- Additive Haar pushforward by an actual affine map, from scalar scaling. -/
theorem map_haar (ν : Measure K) [IsAddHaarMeasure ν]
    (χ : K →*₀ ℝ≥0)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    (μ : Measure (Fin n → K)) [IsAddHaarMeasure μ]
    (A : GeneralLinear n K) (v : Fin n → K) :
    μ.map (measurableEquiv A v) = (χ A.val.det)⁻¹ • μ := by
  have hm : Measurable (A.val.mulVec) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have ht : Measurable (fun x : Fin n → K => x + v) :=
    (continuous_id.add continuous_const).measurable
  have hlin : μ.map A.val.mulVec = (χ A.val.det)⁻¹ • μ := by
    exact HarmonicAnalysis.haarMeasure_map_in_coordinates ν χ hχ
      (ContinuousAddEquiv.refl (Fin n → K)) μ (GeneralLinear.determinant A).ne_zero
  change μ.map ((fun x : Fin n → K => x + v) ∘ A.val.mulVec) = _
  rw [← Measure.map_map ht hm, hlin, Measure.map_smul _ ht.aemeasurable,
    map_add_right_eq_self μ v]

/-- The inverse affine map has the reciprocal determinant factor. -/
theorem map_haar_symm (ν : Measure K) [IsAddHaarMeasure ν]
    (χ : K →*₀ ℝ≥0)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    (μ : Measure (Fin n → K)) [IsAddHaarMeasure μ]
    (A : GeneralLinear n K) (v : Fin n → K) :
    μ.map (measurableEquiv A v).symm = χ A.val.det • μ := by
  rw [measurableEquiv_symm, map_haar ν χ hχ]
  have hd : (A⁻¹).val.det = A.val.det⁻¹ := by
    change ((GeneralLinear.determinant (A⁻¹) : Kˣ) : K) =
      ((GeneralLinear.determinant A : Kˣ) : K)⁻¹
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [hd, map_inv₀, inv_inv]

end Haar

/-- The exact residue-normalized affine Haar law in the supplied p-adic topology. -/
theorem padic_map_haar {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [IsAddHaarMeasure μ]
      (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier),
      μ.map (measurableEquiv A v) =
        ((T.determinantNorm n A : ℝ≥0)⁻¹) • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro _ _ μ _ A v
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T addHaar (Units.mk0 a ha)
  exact map_haar addHaar T.normalizedAbsHom hχ μ A v

/-- The inverse affine Haar law, with the same actual p-adic measure. -/
theorem padic_map_haar_symm {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [IsAddHaarMeasure μ]
      (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier),
      μ.map (measurableEquiv A v).symm =
        (T.determinantNorm n A : ℝ≥0) • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v
  rw [measurableEquiv_symm, padic_map_haar F T n]
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv]

end Langlands.AffineChangeOfVariables
