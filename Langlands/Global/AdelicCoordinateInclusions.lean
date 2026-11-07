import Langlands.Global.Adelic

/-! # Shared additive coordinate inclusions into the actual adeles -/

noncomputable section

open Filter Topology
open scoped RestrictedProduct

universe u

namespace Langlands.Global.HeckeFunctionalEquation

variable (K : Type u) [Field K] [NumberField K]

local instance adelicAdditiveFiniteDecidableEq : DecidableEq (FinitePlace K) := Classical.decEq _
local instance adelicAdditiveInfiniteDecidableEq : DecidableEq (InfinitePlace K) := Classical.decEq _

/-- Insert one additive finite coordinate, with zero at every other place. -/
def finiteAdditiveInclusion (v : FinitePlace K) : FiniteCompletion K v →+ Adeles K :=
  (0 : FiniteCompletion K v →+ InfiniteAdeles K).prod
    (RestrictedProduct.singleAddMonoidHom (fun w : FinitePlace K =>
      w.adicCompletionIntegers K) v)

theorem continuous_finiteAdditiveInclusion (v : FinitePlace K) :
    Continuous (finiteAdditiveInclusion K v) := by
  let S : Set (FinitePlace K) := {v}ᶜ
  let f : FiniteCompletion K v →
      Πʳ w : FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]_[Filter.principal S] :=
    fun x => ⟨Pi.single v x, fun w hw => by
      have h : w ≠ v := by simpa [S] using hw
      simp [Pi.single_eq_of_ne h]⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

/-- Insert one additive infinite coordinate, with zero at every other place. -/
def infiniteAdditiveInclusion (v : InfinitePlace K) : InfiniteCompletion K v →+ Adeles K :=
  (AddMonoidHom.single (fun w : InfinitePlace K => InfiniteCompletion K w) v).prod 0

theorem continuous_infiniteAdditiveInclusion (v : InfinitePlace K) :
    Continuous (infiniteAdditiveInclusion K v) :=
  (continuous_single v).prodMk continuous_const

end Langlands.Global.HeckeFunctionalEquation
