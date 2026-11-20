import Langlands.Global.FiniteParametrizedBlockInduction

/-! Linear coefficient evaluations give an intertwiner into the actual section model. -/

noncomputable section
set_option autoImplicit false

universe u uV uW

namespace Langlands.Global.FiniteParametrizedBlockInduction

open GeneralLinear _root_.Representation

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (V i))
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (FiniteAdelicGL F n) W}

local instance sectionIntertwinerEquivariantGroup :
    AddCommGroup (Induction.EquivariantFunctions (parabolic F B) (coefficient F B σ)) :=
  Submodule.addCommGroup _

local instance sectionIntertwinerSmoothGroup : AddCommGroup (Sections F B σ) :=
  Submodule.addCommGroup _

variable (hρ : IsSmooth ρ)
  (e : standardInfiniteCompact F n → FiniteAdelicGL F n → (W →ₗ[ℂ] PiTensorProduct ℂ V))
  (hcov : ∀ k (p : AdelicBlockParabolic.Finite F B) g x,
    e k (p.val * g) x = finiteCoefficient F B σ p (e k g x))
  (htrans : ∀ k g d x, e k g (ρ d x) = e k (g * d) x)

private def sectionFromLinearEvaluation (x : W) : Sections F B σ :=
  sectionOf F B σ (fun k g => e k g x) (fun k p g => hcov k p g x) (hρ x).choose
    (fun l k g => by
      have hl : ρ l.val x = x := (hρ x).choose_spec l
      rw [← htrans, hl])

/-- Pointwise linear evaluations that obey covariance and right translation give
an intertwiner to the normalized parametrized sections. A stabilizer of the
source vector fixes the entire section. -/
def linearEvaluationIntertwiner : Representation.IntertwiningMap ρ (induced F B σ) where
  toLinearMap :=
    { toFun := sectionFromLinearEvaluation B σ hρ e hcov htrans
      map_add' := fun x y => sections_ext F B σ fun k g => (e k g).map_add x y
      map_smul' := fun c x => sections_ext F B σ fun k g => (e k g).map_smul c x }
  isIntertwining' d := by
    apply LinearMap.ext
    intro x
    apply sections_ext F B σ
    intro k g
    simp only [LinearMap.comp_apply, evaluate_induced]
    exact htrans k g d x

@[simp] theorem evaluate_linearEvaluationIntertwiner (x : W) (k : standardInfiniteCompact F n)
    (g : FiniteAdelicGL F n) :
    evaluate F B σ (linearEvaluationIntertwiner B σ hρ e hcov htrans x) k g = e k g x :=
  rfl

/-- The kernel is detected by vanishing of all the pointwise evaluations. -/
theorem linearEvaluationIntertwiner_eq_zero_iff (x : W) :
    linearEvaluationIntertwiner B σ hρ e hcov htrans x = 0 ↔ ∀ k g, e k g x = 0 :=
  ⟨fun h k g => congrArg (fun z => evaluate F B σ z k g) h,
    fun h => sections_ext F B σ fun k g => h k g⟩

end Langlands.Global.FiniteParametrizedBlockInduction
