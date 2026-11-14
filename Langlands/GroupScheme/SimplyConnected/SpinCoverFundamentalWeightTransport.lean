import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.RepresentedSubgroup

/-!
# Transport of fundamental weights trivial on a kernel

The all-test-scheme alignment predicate is invariant under postcomposition
by a group-scheme monomorphism. In particular, it is preserved by an
isomorphism of targets and by an identity-component inclusion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Kernel

variable {S : Scheme.{u}} {G H H' : GroupScheme S}

/-- The full kernel of a monomorphically postcomposed homomorphism is the
original kernel, with its inclusion into the source preserved. -/
def kernelPostcompIso (π : G ⟶ H) (j : H ⟶ H') [Mono j.hom.hom] :
    kernel (π ≫ j) ≅ kernel π :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (kernelι (π ≫ j)))
    ⟨inferInstance, rfl⟩ ⟨inferInstance, (range_kernelι_comp_mono π j).symm⟩

@[reassoc]
theorem kernelPostcompIso_hom_ι (π : G ⟶ H) (j : H ⟶ H') [Mono j.hom.hom] :
    (kernelPostcompIso π j).hom ≫ kernelι π = kernelι (π ≫ j) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
    (F := SubgroupFunctor.range (kernelι (π ≫ j)))
    ⟨inferInstance, rfl⟩ ⟨inferInstance, (range_kernelι_comp_mono π j).symm⟩

end Kernel

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G H H' : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} {v : d.Vertex} {π : G ⟶ H}

/-- Alignment of a composite implies alignment before postcomposition. -/
theorem FundamentalWeightTrivialOnKernel.of_comp (j : H ⟶ H')
    (h : d.FundamentalWeightTrivialOnKernel v (π ≫ j)) :
    d.FundamentalWeightTrivialOnKernel v π := by
  intro χ hχ hχ' U t ht
  apply h χ hχ hχ' U t
  rw [← Category.assoc, Functor.map_comp, Grp.comp_hom_hom,
    ← Category.assoc, ht, MonObj.one_comp]

/-- A monomorphic postcomposition does not enlarge the tested kernel. -/
theorem FundamentalWeightTrivialOnKernel.comp_mono (j : H ⟶ H')
    [Mono j.hom.hom] (h : d.FundamentalWeightTrivialOnKernel v π) :
    d.FundamentalWeightTrivialOnKernel v (π ≫ j) := by
  intro χ hχ hχ' U t ht
  apply h χ hχ hχ' U t
  have : Mono
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map j).hom.hom := by
    change Mono ((Over.pullback (algebraBaseMap K (SeparableClosure K))).map j.hom.hom)
    infer_instance
  apply (cancel_mono
    ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map j).hom.hom).mp
  simpa only [Category.assoc, Functor.map_comp, Grp.comp_hom_hom,
    MonObj.one_comp] using ht

/-- The alignment predicate is unchanged by a monomorphism of targets. -/
theorem fundamentalWeightTrivialOnKernel_comp_mono_iff (j : H ⟶ H')
    [Mono j.hom.hom] :
    d.FundamentalWeightTrivialOnKernel v (π ≫ j) ↔
      d.FundamentalWeightTrivialOnKernel v π :=
  ⟨fun h => h.of_comp j, fun h => h.comp_mono j⟩

/-- In particular, an isomorphism of targets preserves alignment. -/
theorem FundamentalWeightTrivialOnKernel.comp_iso (e : H ≅ H')
    (h : d.FundamentalWeightTrivialOnKernel v π) :
    d.FundamentalWeightTrivialOnKernel v (π ≫ e.hom) := by
  have : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
  exact h.comp_mono e.hom

/-- Including the identity component preserves the alignment predicate. -/
theorem FundamentalWeightTrivialOnKernel.comp_identityComponentι
    [IsAffineHom H.X.hom] [Smooth H.X.hom] {p : G ⟶ identityComponent H}
    (h : d.FundamentalWeightTrivialOnKernel v p) :
    d.FundamentalWeightTrivialOnKernel v (p ≫ identityComponentι H) := by
  have : Mono (identityComponentι H).hom.hom := Over.mono_of_mono_left _
  exact h.comp_mono (identityComponentι H)

end TitsIndexData

end Langlands.GroupScheme
