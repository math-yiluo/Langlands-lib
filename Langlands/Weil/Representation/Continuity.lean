import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Continuity and inertia kernels of finite-dimensional complex representations

These are proposition targets for a topological group with an open, compact,
nonarchimedean subgroup. The subgroup can later be instantiated by local inertia.
No field-theoretic construction or identification of a Weil group is assumed here.
-/

namespace Langlands.Weil

universe uW uV

/-- The finite-dimensional continuity bridge, including the topological condition
needed to recover continuity from finite inertia image. -/
def RepresentationContinuity : Prop :=
  ∀ (W : Type uW) [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    (I : OpenSubgroup W) [NonarchimedeanGroup I] [CompactSpace I]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ W V),
    let continuousOperators :=
      Continuous (fun w : W => (ρ w).toContinuousLinearMap)
    let inertiaKernel := (ρ.comp I.toSubgroup.subtype).ker
    (continuousOperators ↔ ∀ v : V, Continuous (fun w : W => ρ w v)) ∧
    (continuousOperators ↔ Continuous (fun x : W × V => ρ x.1 x.2)) ∧
    (continuousOperators ↔ IsOpen (inertiaKernel : Set I)) ∧
    (continuousOperators ↔ IsOpen (ρ.ker : Set W)) ∧
    (IsOpen (inertiaKernel : Set I) ↔
      (Set.range (fun i : I => ρ (i : W))).Finite ∧
        IsClosed (inertiaKernel : Set I))

end Langlands.Weil
