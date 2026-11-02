import Langlands.CategoryTheory.RenardSubobjectQuotientStatements

/-! Proof of Renard 2026, Appendix A.VI.2(2–3): the kernel–cokernel correspondence
between subobject and quotient classes, and the binary lattice laws. -/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- Renard A.VI.2(2–3): the kernel and cokernel maps are mutually inverse and
order-reversing on subobject and quotient classes, are given on representatives by
the actual kernel and cokernel maps, and binary intersections and sums of subobjects
are their infimum and supremum. -/
theorem subobjectQuotientAndLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] :
    SubobjectQuotientAndLatticeStatement C := by
  refine ⟨fun X => ?_, fun X P Q => ⟨fun R => le_inf_iff, fun R => sup_le_iff⟩⟩
  let e := Abelian.subobjectIsoSubobjectOp X
  refine ⟨fun P => e.symm_apply_apply P,
    fun K => e.apply_symm_apply (OrderDual.toDual K),
    fun P Q => (e.le_iff_le (x := P) (y := Q)).symm,
    fun K L => (e.symm.le_iff_le (x := OrderDual.toDual L) (y := OrderDual.toDual K)).symm, ?_, ?_⟩
  · intro Y i _
    rfl
  · intro Y p _
    rfl

end Langlands.Renard
