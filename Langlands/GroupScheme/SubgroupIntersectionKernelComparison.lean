import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.AbelianScheme.KernelBaseChange

/-! # Kernels of restrictions and actual subgroup intersections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H D G Q : GroupScheme S}

/-- The first projection of the actual pullback represents the inverse image
of the second subgroup's full range on every test scheme. -/
theorem range_subgroupIntersectionFst_eq_comap (i : H ⟶ G) (d : D ⟶ G) :
    SubgroupFunctor.range (subgroupIntersectionFst i d) =
      (SubgroupFunctor.range d).comap i := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  change (∃ y : U ⟶ (subgroupIntersection i d).X,
      y ≫ (subgroupIntersectionFst i d).hom.hom = x) ↔
    ∃ z : U ⟶ D.X, z ≫ d.hom.hom = x ≫ i.hom.hom
  let hp := subgroupIntersection_isPullback i d
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (subgroupIntersectionSnd i d).hom.hom, ?_⟩
    rw [Category.assoc, ← hp.w, ← Category.assoc]
  · rintro ⟨z, hz⟩
    exact ⟨hp.lift x z hz.symm, hp.lift_fst x z hz.symm⟩

/-- The full kernel of a composite is the inverse image of the full kernel
of the second homomorphism. -/
theorem range_kernelι_comp_eq_comap (i : H ⟶ G) (q : G ⟶ Q) :
    SubgroupFunctor.range (kernelι (i ≫ q)) =
      (SubgroupFunctor.range (kernelι q)).comap i := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_comap, mem_range_kernelι_iff, mem_range_kernelι_iff]
  simp only [Grp.comp_hom_hom, Category.assoc]

/-- If `d` presents the full kernel of `q`, the kernel of its restriction
along `i` is the actual pullback of `d` along `i`. -/
def kernelCompositeIntersectionIso (i : H ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hd : IsClosedSubgroup d)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d) :
    kernel (i ≫ q) ≅ subgroupIntersection i d := by
  let : IsClosedImmersion (subgroupIntersectionFst i d).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst i hd
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := (SubgroupFunctor.range d).comap i)
    ⟨inferInstance, by rw [range_kernelι_comp_eq_comap, hker]⟩
    ⟨Over.mono_of_mono_left _, range_subgroupIntersectionFst_eq_comap i d⟩

/-- The kernel/intersection comparison respects the maps into the source
of the restricted homomorphism. -/
@[reassoc]
theorem kernelCompositeIntersectionIso_hom_comp
    (i : H ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hd : IsClosedSubgroup d)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d) :
    (kernelCompositeIntersectionIso i d q hd hker).hom ≫
      subgroupIntersectionFst i d = kernelι (i ≫ q) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Base

section Field

variable {k : Type u} [Field k]
    {H D G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual kernel of a restricted quotient is a torus whenever its
actual intersection with the supplied full kernel is a torus. -/
theorem isTorus_kernel_comp_of_isTorus_intersection
    (i : H ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hd : IsClosedSubgroup d)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d)
    (hI : IsTorus (subgroupIntersection i d)) :
    IsTorus (kernel (i ≫ q)) :=
  IsTorus.of_iso (kernelCompositeIntersectionIso i d q hd hker) hI

/-- The same torus-kernel conclusion holds after every field extension,
using the actual base-change kernel comparison. -/
theorem isTorus_kernel_comp_baseChange_of_isTorus_intersection
    (i : H ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hd : IsClosedSubgroup d)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range d)
    (hI : IsTorus (subgroupIntersection i d))
    (E : Type u) [Field E] [Algebra k E] :
    IsTorus (kernel ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map (i ≫ q))) := by
  have hK : IsTorus (kernel (i ≫ q)) :=
    isTorus_kernel_comp_of_isTorus_intersection i d q hd hker hI
  exact IsTorus.of_iso (kernelBaseChangeIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) (i ≫ q)).symm hK.baseChange

end Field

end Langlands.GroupScheme
