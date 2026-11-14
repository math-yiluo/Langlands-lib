import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient

/-! # Finite-kernel homomorphisms from smooth connected affine field groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option linter.defProp false in
/-- A homomorphism from a smooth connected affine field group to an affine
finite-type field group is finite whenever its actual kernel is finite. -/
@[instance_reducible]
def isFinite_hom_of_finite_kernel
    {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ P)
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType P.X.hom] [IsAffineHom P.X.hom]
    [IsFinite (kernel f).X.hom] : IsFinite f.hom.hom.left := by
  obtain ⟨I, i, p, hi, hpi, hpF, hpS, hpQ, -, -, -, -⟩ := HomImage.exists_image f
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hk : SubgroupFunctor.range (kernelι p) =
      SubgroupFunctor.range (kernelι f) := by
    rw [← hpi, range_kernelι_comp_mono]
  have hr : (SubgroupFunctor.range (kernelι f)).IsRepresentedBy (kernelι p) :=
    ⟨inferInstance, hk⟩
  have hr' : (SubgroupFunctor.range (kernelι f)).IsRepresentedBy (kernelι f) :=
    ⟨inferInstance, rfl⟩
  let e : kernel p ≅ kernel f := hr.isoOfIsRepresentedBy hr'
  let : IsIso e.hom.hom.hom := (Grp.forget (Over _)).map_isIso e.hom
  let : IsIso e.hom.hom.hom.left := (Over.forget _).map_isIso e.hom.hom.hom
  let : IsFinite (kernel p).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  let : Flat p.hom.hom.left := hpF
  let : Surjective p.hom.hom.left := hpS
  let : QuasiCompact p.hom.hom.left := hpQ
  let : IsFinite p.hom.hom.left := isFinite_of_finite_kernel p
  rw [← hpi]
  change IsFinite (p.hom.hom.left ≫ i.hom.hom.left)
  infer_instance

end Langlands.GroupScheme
