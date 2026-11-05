import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.Representation.Tensor.UnitaryProof
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Positive integral forms on finite algebraic smooth families

Scalar pairings are smooth by the finite tensor model. Their integrals define
a positive Hermitian core without a topology on the coefficient module.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct ContDiff ComplexConjugate BoundedContinuousFunction

namespace Langlands.Plancherel

open FiniteTensor.InvariantPositiveFormProof

universe uJ uV uW uS

variable {J : Type uJ} [Fintype J]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The scalar Hermitian pairing of two finite algebraic smooth families is
smooth. The coefficient module carries no assumed norm or topology. -/
theorem isSmoothFiniteTorusFunction_core_pairing
    (b : InnerProductSpace.Core ℂ V)
    {F H : (J → Circle) → V}
    (hF : F ∈ finiteSmoothFamilies J V) (hH : H ∈ finiteSmoothFamilies J V) :
    IsSmoothFiniteTorusFunction (fun z => b.inner (F z) (H z)) := by
  rw [← range_smoothTensorEvaluation] at hF hH
  obtain ⟨t, rfl⟩ := hF
  obtain ⟨u, rfl⟩ := hH
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
    induction u using TensorProduct.inductionOn with
    | tmul g w =>
      simp only [smoothTensorEvaluation_tmul, b.smul_left, core_inner_smul_right]
      change ContDiff ℝ ∞
        (fun x => conj (f.val (finiteTorusExp x)) *
          ((g.val (finiteTorusExp x)) * b.inner v w))
      have hf : IsSmoothFiniteTorusFunction f.val := f.property
      have hg : IsSmoothFiniteTorusFunction g.val := g.property
      change ContDiff ℝ ∞ (f.val ∘ finiteTorusExp) at hf
      change ContDiff ℝ ∞ (g.val ∘ finiteTorusExp) at hg
      exact (Complex.conjCLE.contDiff.comp hf).mul (hg.mul contDiff_const)
    | add u u' hu hu' =>
      simp only [map_add, Pi.add_apply, core_inner_add_right]
      exact hu.add hu'
  | add t t' ht ht' =>
    simp only [map_add, Pi.add_apply, b.add_left]
    exact ht.add ht'

/-- Compactness of the parameter torus makes every scalar pairing integrable
against any finite Borel measure. -/
theorem integrable_finiteSmoothFamily_core_pairing
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] (F H : finiteSmoothFamilies J V) :
    Integrable (fun z => b.inner (F.val z) (H.val z)) μ :=
  BoundedContinuousFunction.integrable μ
    (BoundedContinuousFunction.mkOfCompact
      ⟨_, (isSmoothFiniteTorusFunction_core_pairing b F.property H.property).continuous⟩)

/-- The actual integral pairing is positive definite when the finite measure
assigns positive measure to every nonempty open subset of the parameter torus. -/
@[instance_reducible]
def finiteSmoothFamilyCore
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    InnerProductSpace.Core ℂ (finiteSmoothFamilies J V) where
  inner F H := ∫ z, b.inner (F.val z) (H.val z) ∂μ
  conj_inner_symm F H := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      b.conj_inner_symm (F.val z) (H.val z))
  re_inner_nonneg F := by
    rw [← integral_re (integrable_finiteSmoothFamily_core_pairing b μ F F)]
    exact integral_nonneg fun z => b.re_inner_nonneg (F.val z)
  add_left F H L := by
    change (∫ z, b.inner (F.val z + H.val z) (L.val z) ∂μ) = _
    simp_rw [b.add_left]
    exact integral_add (integrable_finiteSmoothFamily_core_pairing b μ F L)
      (integrable_finiteSmoothFamily_core_pairing b μ H L)
  smul_left F H c := by
    change (∫ z, b.inner (c • F.val z) (H.val z) ∂μ) = _
    simp_rw [b.smul_left]
    exact integral_const_mul _ _
  definite F hF := by
    let : InnerProductSpace.Core ℂ V := b
    have hzero : (∫ z, (b.inner (F.val z) (F.val z)).re ∂μ) = 0 := by
      change (∫ z, RCLike.re (b.inner (F.val z) (F.val z)) ∂μ) = 0
      rw [integral_re (integrable_finiteSmoothFamily_core_pairing b μ F F), hF]
      rfl
    have hae : (fun z => (b.inner (F.val z) (F.val z)).re) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun z => b.re_inner_nonneg (F.val z))
        (integrable_finiteSmoothFamily_core_pairing b μ F F).re).mp hzero
    have hcont : Continuous (fun z => (b.inner (F.val z) (F.val z)).re) :=
      Complex.continuous_re.comp
        (isSmoothFiniteTorusFunction_core_pairing b F.property F.property).continuous
    have heq := Measure.eq_of_ae_eq hae hcont continuous_const
    apply Subtype.ext
    funext z
    exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp (congrFun heq z)

@[simp]
theorem finiteSmoothFamilyCore_inner
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (F H : finiteSmoothFamilies J V) :
    (finiteSmoothFamilyCore b μ).inner F H =
      ∫ z, b.inner (F.val z) (H.val z) ∂μ := rfl

/-- A fixed coefficient map acts pointwise on the actual finite smooth families. -/
def finiteSmoothFamilyMap (T : V →ₗ[ℂ] W) :
    finiteSmoothFamilies J V →ₗ[ℂ] finiteSmoothFamilies J W where
  toFun F := ⟨fun z => T (F.val z), mem_finiteSmoothFamilies_linearMap F.property T⟩
  map_add' F H := by
    apply Subtype.ext
    funext z
    exact map_add T _ _
  map_smul' c F := by
    apply Subtype.ext
    funext z
    exact map_smul T c _

@[simp]
theorem finiteSmoothFamilyMap_apply (T : V →ₗ[ℂ] W)
    (F : finiteSmoothFamilies J V) (z : J → Circle) :
    (finiteSmoothFamilyMap T F).val z = T (F.val z) := rfl

/-- A coefficient isometry preserves the whole integrated pairing. -/
theorem finiteSmoothFamilyCore_map
    (b : InnerProductSpace.Core ℂ V) (c : InnerProductSpace.Core ℂ W)
    (μ : Measure (J → Circle)) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (T : V →ₗ[ℂ] W) (hT : ∀ v w, c.inner (T v) (T w) = b.inner v w)
    (F H : finiteSmoothFamilies J V) :
    (finiteSmoothFamilyCore c μ).inner (finiteSmoothFamilyMap T F)
      (finiteSmoothFamilyMap T H) = (finiteSmoothFamilyCore b μ).inner F H := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => hT (F.val z) (H.val z)

local instance finiteSmoothTensorAddCommGroup :
    AddCommGroup (smoothFiniteTorusFunctions J ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

/-- The same positive integral core on the original algebraic tensor of scalar
smooth functions and coefficient vectors, through faithful evaluation. -/
@[instance_reducible]
def finiteSmoothTensorCore
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    InnerProductSpace.Core ℂ (smoothFiniteTorusFunctions J ⊗[ℂ] V) :=
  coreComap (finiteSmoothFamilyCore b μ) (smoothTensorFamilyEquiv J V).toLinearMap
    (smoothTensorFamilyEquiv J V).injective

@[simp]
theorem finiteSmoothTensorCore_inner
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (t u : smoothFiniteTorusFunctions J ⊗[ℂ] V) :
    (finiteSmoothTensorCore b μ).inner t u =
      ∫ z, b.inner (smoothTensorEvaluation J V t z)
        (smoothTensorEvaluation J V u z) ∂μ := rfl

/-- On elementary tensors this is the scalar integral pairing times the
original coefficient pairing. -/
theorem finiteSmoothTensorCore_inner_tmul
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (f g : smoothFiniteTorusFunctions J) (v w : V) :
    (finiteSmoothTensorCore b μ).inner (f ⊗ₜ[ℂ] v) (g ⊗ₜ[ℂ] w) =
      (∫ z, conj (f.val z) * g.val z ∂μ) * b.inner v w := by
  rw [finiteSmoothTensorCore_inner]
  simp_rw [smoothTensorEvaluation_tmul, b.smul_left, core_inner_smul_right,
    ← mul_assoc]
  exact integral_mul_const _ _

/-- Restriction to the existing equivariant finite smooth families retains
the supplied, possibly nontrivial, coefficient covariance law. -/
@[instance_reducible]
def finiteSmoothEquivariantFamilyCore
    {S : Type uS} [Group S] (τ : S →* (J → Circle))
    (ρ : Representation ℂ S V)
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    InnerProductSpace.Core ℂ (finiteSmoothEquivariantFamilies J V τ ρ) :=
  coreComap (finiteSmoothFamilyCore b μ)
    (Submodule.inclusion (show finiteSmoothEquivariantFamilies J V τ ρ ≤
      finiteSmoothFamilies J V from fun _ hF => hF.1))
    (Submodule.inclusion_injective _)

@[simp]
theorem finiteSmoothEquivariantFamilyCore_inner
    {S : Type uS} [Group S] (τ : S →* (J → Circle))
    (ρ : Representation ℂ S V)
    (b : InnerProductSpace.Core ℂ V) (μ : Measure (J → Circle))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (F H : finiteSmoothEquivariantFamilies J V τ ρ) :
    (finiteSmoothEquivariantFamilyCore τ ρ b μ).inner F H =
      ∫ z, b.inner (F.val z) (H.val z) ∂μ := rfl

end Langlands.Plancherel
