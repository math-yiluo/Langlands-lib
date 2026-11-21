import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Global.AdelicFunctoriality.Trace

/-! # The standard adelic additive character and relative trace -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open NumberField Global Global.AdelicFunctoriality Global.HeckeFunctionalEquation
open Automorphic.CuspidalWhittaker
open scoped NumberField

universe u v

section Trace

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private theorem infiniteAdeleTrace_algebraMap (r : L) :
    infiniteAdeleTrace (K := K) (algebraMap L (InfiniteAdeleRing L) r) =
      algebraMap K (InfiniteAdeleRing K) (Algebra.trace K L r) :=
  congrArg Prod.fst (adeleTrace_principal (K := K) r)

private theorem absoluteInfiniteTrace_relativeTrace (x : InfiniteAdeleRing L) :
    infiniteTrace K (infiniteAdeleTrace x) = infiniteTrace L x := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap L).equalizer
    ((continuous_infiniteTrace K).comp (continuous_infiniteAdeleTrace (K := K) (L := L)))
    (continuous_infiniteTrace L) (by
      funext r
      change infiniteTrace K (infiniteAdeleTrace (algebraMap L (InfiniteAdeleRing L) r)) =
        infiniteTrace L (algebraMap L (InfiniteAdeleRing L) r)
      rw [infiniteAdeleTrace_algebraMap, infiniteTrace_algebraMap, infiniteTrace_algebraMap,
        Algebra.trace_trace])
  exact congrFun h x

private theorem finiteAdeleTrace_mem_integralFiniteAdeles {a : FiniteAdeles L}
    (ha : a ∈ integralFiniteAdeles L) :
    finiteAdeleTrace (K := K) a ∈ integralFiniteAdeles K := by
  refine (mem_integralFiniteAdeles K _).mpr fun p => ?_
  exact finiteTraceComponent_integral p (fun q => a q)
    (fun q => (mem_integralFiniteAdeles L a).mp ha q.1)

end Trace

/-- For any extension of number fields, the standard adelic character upstairs
is the pullback of the standard character downstairs along the actual adelic trace. -/
def StandardAdelicTraceCharacterStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L],
  ∀ a : Adeles L,
    traceAdditiveCharacter (standardGlobalAdditiveCharacter K)
      (standardGlobalAdditiveCharacter_diagonal K) a = standardGlobalAdditiveCharacter L a

theorem standardAdelicTraceCharacter : StandardAdelicTraceCharacterStatement.{u, v} := by
  intro K L _ _ _ _ _ a
  obtain ⟨r, hr⟩ := exists_sub_mem_integralFiniteAdeles a.2
  have hshift : (adeleTrace (K := K) a).2 -
      algebraMap K (FiniteAdeles K) (Algebra.trace K L r) ∈ integralFiniteAdeles K := by
    rw [adeleTrace_snd, ← finiteAdeleTrace_principal (K := K) r, ← map_sub]
    exact finiteAdeleTrace_mem_integralFiniteAdeles hr
  rw [traceAdditiveCharacter_apply, standardGlobalAdditiveCharacter_apply,
    standardGlobalAdditiveCharacter_apply, adelicCharacter_apply K _ _ hshift,
    adelicCharacter_apply L _ _ hr, adeleTrace_fst,
    ← infiniteAdeleTrace_algebraMap (K := K) r, ← map_sub, absoluteInfiniteTrace_relativeTrace]

end Langlands.BaseChange
