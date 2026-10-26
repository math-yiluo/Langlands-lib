import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The Hilbert completion associated to an invariant positive form
-/

noncomputable section

namespace Langlands.InvariantPositiveForm

universe uG uV

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- A separate copy of the algebraic carrier, with norm determined by the form. -/
def NormedCarrier (_b : InvariantPositiveForm ρ) : Type uV := V

instance (b : InvariantPositiveForm ρ) : AddCommGroup b.NormedCarrier :=
  inferInstanceAs (AddCommGroup V)

instance (b : InvariantPositiveForm ρ) : Module ℂ b.NormedCarrier :=
  inferInstanceAs (Module ℂ V)

instance (b : InvariantPositiveForm ρ) : NormedAddCommGroup b.NormedCarrier :=
  letI : InnerProductSpace.Core ℂ b.NormedCarrier := b.toInnerProductCore
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance (b : InvariantPositiveForm ρ) : InnerProductSpace ℂ b.NormedCarrier :=
  letI : InnerProductSpace.Core ℂ b.NormedCarrier := b.toInnerProductCore
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ b.NormedCarrier)

/-- Identification with the form-dependent normed carrier; it gives no topology to `V`. -/
def toNormedCarrier (b : InvariantPositiveForm ρ) : V ≃ₗ[ℂ] b.NormedCarrier :=
  LinearEquiv.refl ℂ V

@[simp]
theorem inner_toNormedCarrier (b : InvariantPositiveForm ρ) (v w : V) :
    inner ℂ (b.toNormedCarrier v) (b.toNormedCarrier w) = b.inner v w := rfl

theorem norm_toNormedCarrier (b : InvariantPositiveForm ρ) (v : V) :
    ‖b.toNormedCarrier v‖ = Real.sqrt (b.inner v v).re := rfl

/-- The actual uniform completion, with its complete complex inner-product structure. -/
abbrev HilbertCompletion (b : InvariantPositiveForm ρ) : Type uV :=
  UniformSpace.Completion b.NormedCarrier

/-- The canonical complex-linear map from the original algebraic space. -/
def toHilbert (b : InvariantPositiveForm ρ) : V →ₗ[ℂ] b.HilbertCompletion :=
  (UniformSpace.Completion.toComplₗᵢ : b.NormedCarrier →ₗᵢ[ℂ] b.HilbertCompletion).toLinearMap.comp
    b.toNormedCarrier.toLinearMap

theorem toHilbert_injective (b : InvariantPositiveForm ρ) :
    Function.Injective b.toHilbert :=
  (UniformSpace.Completion.toComplₗᵢ : b.NormedCarrier →ₗᵢ[ℂ] b.HilbertCompletion).injective.comp
    b.toNormedCarrier.injective

theorem denseRange_toHilbert (b : InvariantPositiveForm ρ) :
    DenseRange b.toHilbert := by
  change DenseRange (((↑) : b.NormedCarrier → b.HilbertCompletion) ∘ b.toNormedCarrier)
  exact UniformSpace.Completion.denseRange_coe.comp b.toNormedCarrier.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

@[simp]
theorem inner_toHilbert (b : InvariantPositiveForm ρ) (v w : V) :
    inner ℂ (b.toHilbert v) (b.toHilbert w) = b.inner v w :=
  UniformSpace.Completion.inner_coe _ _

theorem norm_toHilbert (b : InvariantPositiveForm ρ) (v : V) :
    ‖b.toHilbert v‖ = Real.sqrt (b.inner v v).re := by
  exact (UniformSpace.Completion.norm_coe (b.toNormedCarrier v)).trans
    (b.norm_toNormedCarrier v)

/-- The original operator, now a linear isometry for the norm supplied by `b`. -/
def normedOperator (b : InvariantPositiveForm ρ) (g : G) :
    b.NormedCarrier →ₗᵢ[ℂ] b.NormedCarrier :=
  (b.toNormedCarrier.toLinearMap.comp ((ρ g).comp b.toNormedCarrier.symm.toLinearMap)).isometryOfInner
    (fun v w => b.invariant g v w)

/-- Extension of the actual action operator to the actual completion. -/
def completedLinearMap (b : InvariantPositiveForm ρ) (g : G) :
    b.HilbertCompletion →L[ℂ] b.HilbertCompletion :=
  (b.normedOperator g).toContinuousLinearMap.completion

@[simp]
theorem completedLinearMap_toHilbert (b : InvariantPositiveForm ρ) (g : G) (v : V) :
    b.completedLinearMap g (b.toHilbert v) = b.toHilbert (ρ g v) :=
  ContinuousLinearMap.completion_apply_coe _ _

theorem completedLinearMap_one (b : InvariantPositiveForm ρ) (x : b.HilbertCompletion) :
    b.completedLinearMap 1 x = x := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (b.completedLinearMap 1).continuous continuous_id
  · intro v
    simp

theorem completedLinearMap_mul (b : InvariantPositiveForm ρ) (g k : G)
    (x : b.HilbertCompletion) :
    b.completedLinearMap (g * k) x =
      b.completedLinearMap g (b.completedLinearMap k x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (b.completedLinearMap (g * k)).continuous
      ((b.completedLinearMap g).continuous.comp (b.completedLinearMap k).continuous)
  · intro v
    simp [map_mul, Module.End.mul_apply]

/-- Each completed operator is a complex-linear isometric equivalence, with inverse
the extension of the action of `g⁻¹`. -/
def completedOperator (b : InvariantPositiveForm ρ) (g : G) :
    b.HilbertCompletion ≃ₗᵢ[ℂ] b.HilbertCompletion where
  toLinearMap := (b.completedLinearMap g).toLinearMap
  invFun := b.completedLinearMap g⁻¹
  left_inv x := by
    change b.completedLinearMap g⁻¹ (b.completedLinearMap g x) = x
    rw [← b.completedLinearMap_mul, inv_mul_cancel, b.completedLinearMap_one]
  right_inv x := by
    change b.completedLinearMap g (b.completedLinearMap g⁻¹ x) = x
    rw [← b.completedLinearMap_mul, mul_inv_cancel, b.completedLinearMap_one]
  norm_map' x := by
    refine b.denseRange_toHilbert.induction_on x ?_ ?_
    · exact isClosed_eq (continuous_norm.comp (b.completedLinearMap g).continuous) continuous_norm
    · intro v
      change ‖b.completedLinearMap g (b.toHilbert v)‖ = ‖b.toHilbert v‖
      rw [completedLinearMap_toHilbert]
      change ‖((b.toNormedCarrier (ρ g v)) : b.HilbertCompletion)‖ =
        ‖((b.toNormedCarrier v) : b.HilbertCompletion)‖
      simp only [UniformSpace.Completion.norm_coe, norm_toNormedCarrier, b.invariant]

@[simp]
theorem completedOperator_toHilbert (b : InvariantPositiveForm ρ) (g : G) (v : V) :
    b.completedOperator g (b.toHilbert v) = b.toHilbert (ρ g v) :=
  b.completedLinearMap_toHilbert g v

/-- The representation on the actual complete Hilbert space. -/
def completedRepresentation (b : InvariantPositiveForm ρ) :
    Representation ℂ G b.HilbertCompletion where
  toFun g := (b.completedOperator g).toLinearMap
  map_one' := by
    ext x
    exact b.completedLinearMap_one x
  map_mul' g k := by
    ext x
    exact b.completedLinearMap_mul g k x

theorem completedRepresentation_apply (b : InvariantPositiveForm ρ) (g : G)
    (x : b.HilbertCompletion) :
    b.completedRepresentation g x = b.completedOperator g x := rfl

@[simp]
theorem completedRepresentation_toHilbert (b : InvariantPositiveForm ρ) (g : G) (v : V) :
    b.completedRepresentation g (b.toHilbert v) = b.toHilbert (ρ g v) :=
  b.completedOperator_toHilbert g v

@[simp]
theorem completedOperator_symm (b : InvariantPositiveForm ρ) (g : G) :
    (b.completedOperator g).symm = b.completedOperator g⁻¹ := by
  ext x
  rfl

@[simp]
theorem completedOperator_norm (b : InvariantPositiveForm ρ) (g : G)
    (x : b.HilbertCompletion) : ‖b.completedOperator g x‖ = ‖x‖ :=
  (b.completedOperator g).norm_map x

@[simp]
theorem completedOperator_inner (b : InvariantPositiveForm ρ) (g : G)
    (x y : b.HilbertCompletion) :
    inner ℂ (b.completedOperator g x) (b.completedOperator g y) = inner ℂ x y :=
  (b.completedOperator g).inner_map_map x y

@[simp]
theorem completedRepresentation_norm (b : InvariantPositiveForm ρ) (g : G)
    (x : b.HilbertCompletion) : ‖b.completedRepresentation g x‖ = ‖x‖ :=
  b.completedOperator_norm g x

@[simp]
theorem completedRepresentation_inner (b : InvariantPositiveForm ρ) (g : G)
    (x y : b.HilbertCompletion) :
    inner ℂ (b.completedRepresentation g x) (b.completedRepresentation g y) = inner ℂ x y :=
  b.completedOperator_inner g x y

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Open stabilizers of algebraic vectors, together with the uniform isometry
bound, make every completed orbit continuous for the original topology on `G`. -/
theorem continuous_completedOrbit (b : InvariantPositiveForm ρ) (hρ : IsSmooth ρ)
    (x : b.HilbertCompletion) :
    Continuous (fun g : G => b.completedRepresentation g x) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨v, hv⟩ := b.denseRange_toHilbert.exists_dist_lt x (half_pos hε)
  obtain ⟨K, hK⟩ := hρ v
  have hmem : ∀ᶠ g : G in nhds g₀, g₀⁻¹ * g ∈ K := by
    exact (continuous_const.mul continuous_id).continuousAt.eventually
      (K.isOpen.mem_nhds (by simp))
  filter_upwards [hmem] with g hg
  have hfix : ρ (g₀⁻¹ * g) v = v := hK ⟨g₀⁻¹ * g, hg⟩
  have hsame : b.completedRepresentation g (b.toHilbert v) =
      b.completedRepresentation g₀ (b.toHilbert v) := by
    rw [completedRepresentation_toHilbert, completedRepresentation_toHilbert]
    apply congrArg b.toHilbert
    calc
      ρ g v = ρ g₀ (ρ (g₀⁻¹ * g) v) := by
        simp [← Module.End.mul_apply, ← map_mul]
      _ = ρ g₀ v := by rw [hfix]
  calc
    dist (b.completedRepresentation g x) (b.completedRepresentation g₀ x) ≤
        dist (b.completedRepresentation g x) (b.completedRepresentation g (b.toHilbert v)) +
          dist (b.completedRepresentation g (b.toHilbert v)) (b.completedRepresentation g₀ x) :=
      dist_triangle _ _ _
    _ = dist x (b.toHilbert v) + dist (b.toHilbert v) x := by
      have hd₁ := (b.completedOperator g).isometry.dist_eq x (b.toHilbert v)
      have hd₂ : dist (b.completedRepresentation g (b.toHilbert v))
          (b.completedRepresentation g₀ x) = dist (b.toHilbert v) x := by
        rw [hsame]
        exact (b.completedOperator g₀).isometry.dist_eq _ _
      exact congrArg₂ (· + ·) hd₁ hd₂
    _ < ε := by rw [dist_comm (b.toHilbert v) x]; linarith

end Langlands.InvariantPositiveForm
