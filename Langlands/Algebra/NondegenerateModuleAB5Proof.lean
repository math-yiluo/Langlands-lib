import Langlands.Algebra.NondegenerateModuleAB5Statements
import Langlands.Algebra.NondegenerateModuleSubobject
import Langlands.Algebra.IntegerNonUnitalSubmodule
import Langlands.Algebra.NonUnitalModuleDirectSum
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Bounds.OrderIso

/-! Proof of the actual source AB5 law of Renard I.6. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateModuleAB5Proof

open NondegenerateModuleAB5Statements

universe uA uI uM

/-- Directed sums of ordinary submodules are setwise unions. -/
private theorem inf_iSup_of_directed
    {R : Type uA} [Ring R] {V : Type uM} [AddCommGroup V] [Module R V]
    (I : Type uI) [Nonempty I] (S : I → Submodule R V)
    (hS : Directed (· ≤ ·) S) (N : Submodule R V) :
    N ⊓ (⨆ i, S i) = ⨆ i, N ⊓ S i := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed S hS).1 hx.2
    exact (le_iSup (fun i => N ⊓ S i) i) ⟨hx.1, hi⟩
  · exact iSup_le fun i => inf_le_inf_left N (le_iSup S i)

/-- Transport the actual directed union through the original-range comparison. -/
theorem directedSubobjectDistributivity :
    DirectedSubobjectDistributivity.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  intro M I hI F hF N
  let : Nonempty I := hI
  let := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M.obj))
  let e : Subobject M ≃o Submodule (Unitization ℤ A) M.obj :=
    (NondegenerateModuleCat.subobjectOrderIso hA M).trans
      NonUnitalSubmodule.intUnitizedOrderIso
  have hE : Directed (· ≤ ·) (fun i => e (F i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hF i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  let U : Subobject M := e.symm (⨆ i, e (F i))
  have heU : e U = ⨆ i, e (F i) := e.apply_symm_apply _
  refine ⟨U, ?_, ?_⟩
  · apply (e.isLUB_image (s := Set.range F) (x := ⨆ i, e (F i))).1
    simpa only [← Set.range_comp'] using
      (isLUB_iSup : IsLUB (Set.range (fun i => e (F i))) (⨆ i, e (F i)))
  · have heInf : e (N ⊓ U) = ⨆ i, e (N ⊓ F i) := by
      rw [map_inf, heU]
      simpa only [map_inf] using
        inf_iSup_of_directed (R := Unitization ℤ A) (V := M.obj)
          I (fun i => e (F i)) hE (e N)
    apply (e.isLUB_image' (s := Set.range fun i => N ⊓ F i)).1
    simpa only [← Set.range_comp', heInf] using
      (isLUB_iSup : IsLUB (Set.range (fun i => e (N ⊓ F i)))
        (⨆ i, e (N ⊓ F i)))

/-- The actual direct sum supplies the coproduct clause of source AB5. -/
theorem sourceAB5 : SourceAB5Statement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  refine ⟨?_, directedSubobjectDistributivity.{uA, uI, max uI uM} A hA⟩
  exact hasCoproducts_of_colimit_cofans
    (fun P => NonUnitalModuleDirectSum.cofan.{uA, uI, uM} hA P)
    (fun P => NonUnitalModuleDirectSum.cofanIsColimit.{uA, uI, uM} hA P)

/-- Both exact universally quantified source AB5 targets. -/
theorem ab5Assertions : AB5Assertions.{uA, uI, uM} :=
  ⟨directedSubobjectDistributivity, sourceAB5⟩

example : DirectedSubobjectDistributivity.{uA, uI, uM} :=
  directedSubobjectDistributivity.{uA, uI, uM}
example : SourceAB5Statement.{uA, uI, uM} := sourceAB5.{uA, uI, uM}
example : AB5Assertions.{uA, uI, uM} := ab5Assertions.{uA, uI, uM}
example : AB5Assertions.{0, 1, 0} := ab5Assertions.{0, 1, 0}
example : AB5Assertions.{1, 0, 0} := ab5Assertions.{1, 0, 0}
example : AB5Assertions.{0, 0, 1} := ab5Assertions.{0, 0, 1}

example : AB5Assertions.{0, 1, 2} := ab5Assertions.{0, 1, 2}
example : AB5Assertions.{0, 2, 1} := ab5Assertions.{0, 2, 1}
example : AB5Assertions.{1, 0, 2} := ab5Assertions.{1, 0, 2}
example : AB5Assertions.{1, 2, 0} := ab5Assertions.{1, 2, 0}
example : AB5Assertions.{2, 0, 1} := ab5Assertions.{2, 0, 1}
example : AB5Assertions.{2, 1, 0} := ab5Assertions.{2, 1, 0}

end Langlands.Algebra.NondegenerateModuleAB5Proof
