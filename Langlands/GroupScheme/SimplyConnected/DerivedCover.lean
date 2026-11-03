import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Simply connected covers of actual derived subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G D C : GroupScheme (Spec (CommRingCat.of k))}

/-- Supplied maps from a simply connected group through an actual derived subgroup of a
connected reductive group. The covering condition is imposed on `π : C ⟶ D`. -/
structure IsSimplyConnectedDerivedCover (d : D ⟶ G) (π : C ⟶ D) : Prop where
  isConnectedReductive : IsConnectedReductive G
  isDerivedSubgroup : IsDerivedSubgroup d
  isSimplyConnectedCover : IsSimplyConnectedCover π

namespace IsSimplyConnectedDerivedCover

variable {d : D ⟶ G} {π : C ⟶ D} (h : IsSimplyConnectedDerivedCover d π)

include h

/-- Every point in the range of the ambient composite lies in the derived subgroup. -/
theorem range_comp_le_derivedSubgroup :
    SubgroupFunctor.range (π ≫ d) ≤ derivedSubgroup G := by
  rw [← h.isDerivedSubgroup.2]
  intro T x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y ≫ π.hom.hom, ?_⟩
  change (y ≫ π.hom.hom) ≫ d.hom.hom = x
  exact hy

/-- The inclusion of the derived subgroup does not change which test points are killed. -/
theorem comp_eq_one_iff {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ C.X) :
    x ≫ (π ≫ d).hom.hom = 1 ↔ x ≫ π.hom.hom = 1 := by
  have : Mono d.hom.hom := h.isDerivedSubgroup.isRepresentedBy.1
  change x ≫ (π.hom.hom ≫ d.hom.hom) = 1 ↔ x ≫ π.hom.hom = 1
  constructor
  · intro hx
    apply (cancel_mono d.hom.hom).mp
    simpa only [Category.assoc, MonObj.one_comp] using hx
  · intro hx
    rw [← Category.assoc, hx, MonObj.one_comp]

/-- The two actual kernels have the same full subgroup functor in `C`. -/
theorem kernel_range_eq :
    SubgroupFunctor.range (kernelι (π ≫ d)) = SubgroupFunctor.range (kernelι π) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  exact h.comp_eq_one_iff x

/-- The full kernel of the ambient composite is central in the simply connected source. -/
theorem isCentral_kernel_comp : IsCentral (kernelι (π ≫ d)) := by
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  exact h.isSimplyConnectedCover.isCentralIsogeny.mem_center_of_comp_eq_one
    ((h.comp_eq_one_iff x).mp hx)

/-- The actual ambient-composite kernel is canonically the actual central-cover kernel. -/
def kernelIso : kernel (π ≫ d) ≅ kernel π :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (kernelι π))
    ⟨inferInstance, h.kernel_range_eq⟩ ⟨inferInstance, rfl⟩

/-- The kernel comparison preserves the inclusions into the covering group. -/
@[reassoc]
theorem kernelIso_hom_comp :
    h.kernelIso.hom ≫ kernelι π = kernelι (π ≫ d) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (F := SubgroupFunctor.range (kernelι π))
    ⟨inferInstance, h.kernel_range_eq⟩ ⟨inferInstance, rfl⟩

/-- On every test scheme, the kernel comparison leaves the point in `C` unchanged. -/
theorem kernelIso_hom_points {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (kernel (π ≫ d)).X) :
    (x ≫ h.kernelIso.hom.hom.hom) ≫ (kernelι π).hom.hom =
      x ≫ (kernelι (π ≫ d)).hom.hom := by
  have he := congrArg (fun f => (Grp.forget (Over (Spec (CommRingCat.of k)))).map f)
    h.kernelIso_hom_comp
  change h.kernelIso.hom.hom.hom ≫ (kernelι π).hom.hom =
    (kernelι (π ≫ d)).hom.hom at he
  rw [Category.assoc, he]

/-- The kernel comparison commutes with restriction along every test-scheme morphism. -/
theorem kernelIso_hom_points_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (kernel (π ≫ d)).X) :
    (a ≫ x) ≫ h.kernelIso.hom.hom.hom = a ≫ (x ≫ h.kernelIso.hom.hom.hom) :=
  Category.assoc _ _ _

end IsSimplyConnectedDerivedCover

end Langlands.GroupScheme
