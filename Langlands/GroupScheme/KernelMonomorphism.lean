import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Kernels under monomorphic postcomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Postcomposition by a monomorphism preserves the full scheme-kernel range. -/
theorem range_kernelι_comp_mono {S : Scheme.{u}} {G Q R : GroupScheme S}
    (q : G ⟶ Q) (i : Q ⟶ R) [Mono i.hom.hom] :
    SubgroupFunctor.range (kernelι (q ≫ i)) = SubgroupFunctor.range (kernelι q) := by
  ext T x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  constructor
  · intro hx
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hx, MonObj.one_comp]
  · intro hx
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]

end Langlands.GroupScheme
