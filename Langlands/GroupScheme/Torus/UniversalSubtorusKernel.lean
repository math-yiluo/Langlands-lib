import Langlands.GroupScheme.Torus.UniversalSubtorus
import Langlands.GroupScheme.Torus.RelativeTorusMultiplication

/-! # Universal subtori as kernels of bounded-torsion quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SubgroupFunctor

theorem range_kernel_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {H Q : GroupScheme S} (q : H ⟶ Q) :
    (range (kernelι q)).baseChange b =
      range (kernelι ((GroupScheme.baseChange b).map q)) := by
  rw [← range_baseChangeHom, ← kernelBaseChangeIso_hom_ι b q,
    range_iso_comp]

theorem range_le_kernel_of_comp_eq_one {S : Scheme.{u}} {G H Q : GroupScheme S}
    [IsCommMonObj Q.X]
    (f : G ⟶ H) (q : H ⟶ Q) (hf : f ≫ q = 1) :
    range f ≤ range (kernelι q) := by
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, hf]
  exact MonObj.comp_one y

end SubgroupFunctor

/-- A relative torus which is the full kernel of a bounded-torsion quotient
absorbs all torus homomorphisms universally. -/
theorem isUniversalSubtorus_of_kernel_torsion
    {S : Scheme.{u}} {T H Q : GroupScheme S} [IsCommMonObj Q.X]
    (j : T ⟶ H) (q : H ⟶ Q)
    (hj : IsClosedSubgroup j) (hT : RelativeTorus.IsTorus T)
    (hker : SubgroupFunctor.range j = SubgroupFunctor.range (kernelι q))
    {n : ℤ} (hn : n ≠ 0) (hQ : multiplication Q n = 1) :
    IsUniversalSubtorus j := by
  refine ⟨hj, hT, ?_⟩
  intro S' b T' f hT'
  let F := GroupScheme.baseChange b
  let := hT'.isCommMonObj
  have hQ' : multiplication (F.obj Q) n = 1 := by
    rw [← multiplication_baseChange b Q n, hQ]
    apply Grp.hom_ext
    change (Over.pullback b).map (1 : Q.X ⟶ Q.X) = 1
    exact (Functor.homMonoidHom (Over.pullback b)).map_one
  have hf : f ≫ F.map q = 1 :=
    hT'.hom_eq_one_of_multiplication_eq_one hn hQ' (f ≫ F.map q)
  have hr : SubgroupFunctor.range f ≤ SubgroupFunctor.range (F.map j) := by
    change SubgroupFunctor.range f ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j)
    rw [SubgroupFunctor.range_baseChangeHom, hker,
      SubgroupFunctor.range_kernel_baseChange]
    exact SubgroupFunctor.range_le_kernel_of_comp_eq_one f (F.map q) hf
  have hj' := hj.baseChange b
  have : IsClosedImmersion (F.map j).hom.hom.left := hj'
  have hrep : (SubgroupFunctor.range (F.map j)).IsRepresentedBy (F.map j) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨hrep.factorHom f hr, hrep.factorHom_comp f hr⟩

end Langlands.GroupScheme
