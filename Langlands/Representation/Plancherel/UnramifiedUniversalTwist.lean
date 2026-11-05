import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Langlands.Representation.Plancherel.NormKernelTopologyProof
import Langlands.Representation.Category.Twist
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The concrete universal unramified twist

Over the existing evaluation-generated regular algebra, tensor evaluation
is faithful and has exactly the finite polynomial families as its image.
The scalar-extended action twisted by the evaluation character specializes
to each actual unramified twist. No geometric filtration, continuation
operator, algebraic-torus comparison or rationality theorem is asserted.
-/

noncomputable section

open scoped TensorProduct NNReal BigOperators

namespace Langlands.Plancherel

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
  (V : Type uV) [AddCommGroup V] [Module ℂ V]

local instance unramifiedTensorAddCommGroup :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

/-- Simultaneous specialization of the scalar-extension tensor at all actual
unramified parameters. -/
def unramifiedTensorEvaluation :
    unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[ℂ] (unramifiedCharacters ν → V) :=
  TensorProduct.lift
    { toFun := fun b =>
        { toFun := fun v χ => b.val χ • v
          map_add' := by intros; funext χ; exact smul_add _ _ _
          map_smul' := by intros; funext χ; exact smul_comm _ _ _ }
      map_add' := by intros; ext v χ; exact add_smul _ _ _
      map_smul' := by
        intro c b
        apply LinearMap.ext
        intro v
        funext χ
        exact (smul_smul c (b.val χ) v).symm }

@[simp]
theorem unramifiedTensorEvaluation_tmul
    (b : unramifiedRegularFunctions ν) (v : V) (χ : unramifiedCharacters ν) :
    unramifiedTensorEvaluation ν V (b ⊗ₜ[ℂ] v) χ = b.val χ • v := rfl

theorem unramifiedTensorEvaluation_basisCoord {J : Type*} [DecidableEq J]
    (e : Module.Basis J ℂ V)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) (i : J)
    (χ : unramifiedCharacters ν) :
    (TensorProduct.equivFinsuppOfBasisRight e t i).val χ =
      e.coord i (unramifiedTensorEvaluation ν V t χ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => simp [Module.Basis.coord_apply, mul_comm]
  | add t u ht hu =>
      simp only [map_add, Finsupp.add_apply, Subalgebra.coe_add, Pi.add_apply, ht, hu]

/-- The concrete function algebra makes simultaneous specialization faithful,
also for infinite-dimensional coefficient spaces. -/
theorem unramifiedTensorEvaluation_injective :
    Function.Injective (unramifiedTensorEvaluation ν V) := by
  classical
  let e := Module.Free.chooseBasis ℂ V
  intro t u h
  apply (TensorProduct.equivFinsuppOfBasisRight e).injective
  apply Finsupp.ext
  intro i
  apply Subtype.ext
  funext χ
  rw [unramifiedTensorEvaluation_basisCoord, unramifiedTensorEvaluation_basisCoord, h]

/-- A tensor gives one finite expansion, whose coefficients and fixed vectors
work at every parameter. -/
theorem unramifiedTensorEvaluation_isPolynomialOn
    (Ω : Set (unramifiedCharacters ν))
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) :
    UnramifiedOperatorFamily.IsPolynomialOn Ω
      (fun χ => unramifiedTensorEvaluation ν V t χ.val) := by
  obtain ⟨n, b, v, ht⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨n, b, v, ?_⟩
  intro χ
  rw [ht, map_sum]
  simp

/-- Every finite polynomial expansion on an arbitrary subset is the
restriction of a tensor specialization. No density or uniqueness on that
subset is asserted. -/
theorem isPolynomialOn_iff_exists_unramifiedTensor
    (Ω : Set (unramifiedCharacters ν)) (f : Ω → V) :
    UnramifiedOperatorFamily.IsPolynomialOn Ω f ↔
      ∃ t : unramifiedRegularFunctions ν ⊗[ℂ] V,
        ∀ χ : Ω, unramifiedTensorEvaluation ν V t χ.val = f χ := by
  constructor
  · rintro ⟨n, b, v, hf⟩
    refine ⟨∑ i, b i ⊗ₜ[ℂ] v i, ?_⟩
    intro χ
    simpa using (hf χ).symm
  · rintro ⟨t, ht⟩
    simpa only [ht] using unramifiedTensorEvaluation_isPolynomialOn ν V Ω t

/-- Specialization at one parameter commutes with the regular-algebra scalar
action via actual evaluation of that scalar. -/
theorem unramifiedTensorEvaluation_regular_smul
    (b : unramifiedRegularFunctions ν)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) (χ : unramifiedCharacters ν) :
    unramifiedTensorEvaluation ν V (b • t) χ =
      b.val χ • unramifiedTensorEvaluation ν V t χ := by
  induction t using TensorProduct.inductionOn with
  | tmul c v => simp [TensorProduct.smul_tmul', smul_smul]
  | add t u ht hu => simp only [smul_add, map_add, Pi.add_apply, ht, hu]

variable {V}

/-- Scalar extension of the original representation, twisted by the
evaluation character, as an action linear over the regular algebra. -/
def universalUnramifiedRepresentation (ρ : Representation ℂ G V) :
    Representation (unramifiedRegularFunctions ν) G
      (unramifiedRegularFunctions ν ⊗[ℂ] V) where
  toFun g := unramifiedEvaluationRegular ν g • (ρ g).baseChange _
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [TensorProduct.smul_tmul', smul_smul, mul_comm]

@[simp]
theorem universalUnramifiedRepresentation_tmul (ρ : Representation ℂ G V)
    (g : G) (b : unramifiedRegularFunctions ν) (v : V) :
    universalUnramifiedRepresentation ν ρ g (b ⊗ₜ[ℂ] v) =
      (unramifiedEvaluationRegular ν g * b) ⊗ₜ[ℂ] (ρ g v) := rfl

/-- Every specialization carries the actual twisted action, rather than a
chosen isomorphic replacement. -/
theorem unramifiedTensorEvaluation_action (ρ : Representation ℂ G V)
    (g : G) (t : unramifiedRegularFunctions ν ⊗[ℂ] V)
    (χ : unramifiedCharacters ν) :
    unramifiedTensorEvaluation ν V (universalUnramifiedRepresentation ν ρ g t) χ =
      Langlands.twist χ.val.toMonoidHom ρ g (unramifiedTensorEvaluation ν V t χ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => simp [Langlands.twist, smul_smul, mul_comm]
  | add t u ht hu => simp only [map_add, Pi.add_apply, ht, hu]

/-- All universal evaluation factors are trivial on the full common norm
kernel, not just on a chosen finite subfamily. -/
theorem unramifiedEvaluationRegular_eq_one_of_mem_commonNormKernel
    {g : G} (hg : g ∈ commonNormKernel ν) :
    unramifiedEvaluationRegular ν g = 1 := by
  apply Subtype.ext
  funext χ
  change (χ.val g : ℂ) = 1
  rw [show χ.val g = 1 from χ.property hg]
  rfl

/-- Openness of the full common kernel and smoothness of the original action
give smoothness over the regular algebra. -/
theorem isSmooth_universalUnramifiedRepresentation
    (ρ : Representation ℂ G V) (hρ : Langlands.IsSmooth ρ)
    (hν : IsOpen (commonNormKernel ν : Set G)) :
    Langlands.IsSmooth (R := unramifiedRegularFunctions ν) (G := G)
      (V := unramifiedRegularFunctions ν ⊗[ℂ] V)
      (universalUnramifiedRepresentation ν ρ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul b v =>
    obtain ⟨K, hK⟩ := hρ v
    let H : OpenSubgroup G := ⟨commonNormKernel ν, hν⟩
    refine ⟨K ⊓ H, ?_⟩
    intro g
    change universalUnramifiedRepresentation ν ρ (g : G) (b ⊗ₜ[ℂ] v) = _
    rw [universalUnramifiedRepresentation_tmul,
      unramifiedEvaluationRegular_eq_one_of_mem_commonNormKernel ν g.property.2,
      one_mul]
    have hv : ρ (g : G) v = v := hK ⟨g, g.property.1⟩
    rw [hv]
  | add t u ht hu => exact Langlands.isSmoothVector_add ht hu

/-- For continuous positive norm characters on the same locally compact
nonarchimedean group, the published common-kernel theorem discharges the
openness requirement. -/
theorem isSmooth_universalUnramifiedRepresentation_of_continuous
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (hν : ∀ i, Continuous (ν i))
    (ρ : Representation ℂ G V) (hρ : Langlands.IsSmooth ρ) :
    Langlands.IsSmooth (R := unramifiedRegularFunctions ν) (G := G)
      (V := unramifiedRegularFunctions ν ⊗[ℂ] V)
      (universalUnramifiedRepresentation ν ρ) :=
  isSmooth_universalUnramifiedRepresentation ν ρ hρ
    (commonNormKernelTopology G I ν hν).1

end Langlands.Plancherel
