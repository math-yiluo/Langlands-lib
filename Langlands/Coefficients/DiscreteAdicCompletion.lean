import Langlands.Coefficients.AdicSystem
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Instances.Discrete

/-! # The discrete-quotient topology on the actual adic completion -/

noncomputable section

universe u v w x y

namespace Langlands.Coefficients.DiscreteAdicCompletion

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A type synonym for the actual ideal-power quotient, with its discrete topology. -/
def Reduction (n : ℕ) := M ⧸ (I ^ n • ⊤ : Submodule R M)

instance reductionAddCommGroup (n : ℕ) : AddCommGroup (Reduction I M n) :=
  inferInstanceAs (AddCommGroup (M ⧸ (I ^ n • ⊤ : Submodule R M)))

instance reductionModule (n : ℕ) : Module R (Reduction I M n) :=
  inferInstanceAs (Module R (M ⧸ (I ^ n • ⊤ : Submodule R M)))

instance reductionTopology (n : ℕ) : TopologicalSpace (Reduction I M n) := ⊥

instance reductionDiscreteTopology (n : ℕ) : DiscreteTopology (Reduction I M n) := ⟨rfl⟩

instance reductionFinite (n : ℕ) [Finite (M ⧸ (I ^ n • ⊤ : Submodule R M))] :
    Finite (Reduction I M n) :=
  inferInstanceAs (Finite (M ⧸ (I ^ n • ⊤ : Submodule R M)))

/-- The actual canonical quotient map with the discrete quotient as codomain. -/
def quotient (n : ℕ) : M →ₗ[R] Reduction I M n :=
  Submodule.mkQ (I ^ n • ⊤ : Submodule R M)

/-- The actual transition between discrete ideal-power quotients. -/
def transition {a b : ℕ} (h : a ≤ b) : Reduction I M b →L[R] Reduction I M a where
  toLinearMap := AdicCompletion.transitionMap I M h
  cont := continuous_of_discreteTopology

/-- A type synonym for Mathlib's actual module of compatible quotient sequences. -/
def Completion := AdicCompletion I M

instance completionAddCommGroup : AddCommGroup (Completion I M) :=
  inferInstanceAs (AddCommGroup (AdicCompletion I M))

instance completionModule : Module R (Completion I M) :=
  inferInstanceAs (Module R (AdicCompletion I M))

/-- The canonical linear identification with the existing algebraic completion. -/
def toAdicCompletion : Completion I M ≃ₗ[R] AdicCompletion I M :=
  LinearEquiv.refl R _

/-- The actual inclusion in the product of discrete ideal-power quotients. -/
def inclusion : Completion I M →ₗ[R] ∀ n, Reduction I M n :=
  AdicCompletion.incl I M

instance completionTopology : TopologicalSpace (Completion I M) :=
  TopologicalSpace.induced (inclusion I M) inferInstance

/-- The topology is exactly the product-subtype topology on compatible sequences. -/
theorem inclusion_isEmbedding : Topology.IsEmbedding (inclusion I M) :=
  ⟨⟨rfl⟩, Subtype.val_injective⟩

instance completionT2Space : T2Space (Completion I M) :=
  (inclusion_isEmbedding I M).t2Space

instance completionIsTopologicalAddGroup : IsTopologicalAddGroup (Completion I M) :=
  (inclusion_isEmbedding I M).isInducing.isTopologicalAddGroup (inclusion I M)

/-- The actual evaluation map, now a continuous linear map to the discrete quotient. -/
def eval (n : ℕ) : Completion I M →L[R] Reduction I M n where
  toLinearMap := AdicCompletion.eval I M n
  cont := (continuous_apply (A := fun n => Reduction I M n) n).comp
    (inclusion_isEmbedding I M).continuous

@[simp] theorem eval_apply (n : ℕ) (x : Completion I M) :
    eval I M n x = (toAdicCompletion I M x).val n := rfl

theorem eval_surjective (n : ℕ) : Function.Surjective (eval I M n) :=
  AdicCompletion.eval_surjective I M n

/-- A map into the completion is continuous exactly when all its coordinates are. -/
theorem continuous_iff {X : Type y} [TopologicalSpace X] (f : X → Completion I M) :
    Continuous f ↔ ∀ n, Continuous (fun x => eval I M n (f x)) := by
  rw [(inclusion_isEmbedding I M).isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- Compatible sequences form a closed subset of the product of discrete quotients. -/
theorem compatible_isClosed :
    IsClosed {x : ∀ n, Reduction I M n |
      ∀ (a b : ℕ) (h : a ≤ b), transition I M h (x b) = x a} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun h => ?_
  exact isClosed_eq ((transition I M h).continuous.comp
    (continuous_apply (A := fun n => Reduction I M n) b))
    (continuous_apply (A := fun n => Reduction I M n) a)

instance completionCompactSpace
    [∀ n, Finite (M ⧸ (I ^ n • ⊤ : Submodule R M))] :
    CompactSpace (Completion I M) := by
  let s : Set (∀ n, Reduction I M n) :=
    {x | ∀ (a b : ℕ) (h : a ≤ b), transition I M h (x b) = x a}
  have hs : IsClosed s := compatible_isClosed I M
  have hr : Set.range (inclusion I M) = s := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ a b h
      exact y.property h
    · intro hx
      exact ⟨⟨x, fun {a b} h => hx a b h⟩, rfl⟩
  exact (⟨inclusion_isEmbedding I M, hr ▸ hs⟩ :
    Topology.IsClosedEmbedding (inclusion I M)).compactSpace

variable {M}
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/-- The actual map induced on a discrete quotient by a linear map. -/
def reductionMap (f : M →ₗ[R] N) (n : ℕ) :
    Reduction I M n →L[R] Reduction I N n where
  toLinearMap := (f.reduceModIdeal (I ^ n)).restrictScalars R
  cont := continuous_of_discreteTopology

/-- The existing algebraic completion map is continuous for the discrete-quotient topology. -/
def map (f : M →ₗ[R] N) : Completion I M →L[R] Completion I N where
  toLinearMap := (AdicCompletion.map I f).restrictScalars R
  cont := (continuous_iff I N _).mpr fun n =>
    (reductionMap I f n).continuous.comp (eval I M n).continuous

@[simp] theorem map_eval (f : M →ₗ[R] N) (x : Completion I M) (n : ℕ) :
    eval I N n (map I f x) = f.reduceModIdeal (I ^ n) (eval I M n x) := rfl

@[simp] theorem map_id :
    map I (LinearMap.id (R := R) (M := M)) = ContinuousLinearMap.id R (Completion I M) := by
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun (AdicCompletion.map_id I M) x

@[simp] theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I (g.comp f) = (map I g).comp (map I f) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (AdicCompletion.map_comp_apply I f g x).symm

/-- The original canonical algebraic map into the completion. -/
def of : M →ₗ[R] Completion I M := AdicCompletion.of I M

@[simp] theorem eval_of (n : ℕ) (x : M) :
    eval I M n (of I x) = Submodule.mkQ (I ^ n • ⊤ : Submodule R M) x := rfl

@[simp] theorem map_of (f : M →ₗ[R] N) (x : M) :
    map I f (of I x) = of I (f x) := rfl

/-- Continuity of the original canonical map requires continuity of its quotient maps. -/
theorem of_continuous [TopologicalSpace M]
    (h : ∀ n, Continuous (quotient I M n)) :
    Continuous (of (M := M) I) :=
  (continuous_iff I M _).mpr h

end Langlands.Coefficients.DiscreteAdicCompletion
