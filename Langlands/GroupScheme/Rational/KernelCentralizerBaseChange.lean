import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.KernelCentralizerClosed
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.KernelRepresentativeTransport

/-! # Base change of full character-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

variable {B B' : Scheme.{u}} (b : B' ⟶ B)
    {S : CommGroupScheme B} {G C : GroupScheme B}

/-- An isomorphism on the target of a character leaves its full kernel unchanged. -/
theorem characterKernel_range_baseChange (a : characterLattice S) :
    SubgroupFunctor.range
        (kernelι ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom a))) =
      SubgroupFunctor.range (characterKernelι (characterLattice.baseChange b S a)) := by
  ext V x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  change x ≫ ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom a)).hom.hom = 1 ↔
    x ≫ (((GroupScheme.baseChange b).map (CommGroupScheme.groupHom a)) ≫
      (Gm.baseChangeIso b).hom).hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  constructor
  · intro hx
    rw [hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono (Gm.baseChangeIso b).hom.hom.hom).mp
    rw [hx, MonObj.one_comp]

/-- Base change of the full scheme-theoretic character kernel, including its
possibly nonreduced structure. -/
def characterKernelBaseChangeIso (a : characterLattice S) :
    (GroupScheme.baseChange b).obj (characterKernel a) ≅
      characterKernel (characterLattice.baseChange b S a) :=
  kernelBaseChangeIso b (CommGroupScheme.groupHom a) ≪≫
    KernelRepresentative.iso
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom a))
      (characterKernelι (characterLattice.baseChange b S a))
      (characterKernel_range_baseChange b a)

/-- The full-kernel comparison preserves the actual inclusion into the torus. -/
@[reassoc (attr := simp)]
theorem characterKernelBaseChangeIso_hom_ι (a : characterLattice S) :
    (characterKernelBaseChangeIso b a).hom ≫
        characterKernelι (characterLattice.baseChange b S a) =
      (GroupScheme.baseChange b).map (characterKernelι a) := by
  change (kernelBaseChangeIso b (CommGroupScheme.groupHom a)).hom ≫
    (KernelRepresentative.iso _ _ (characterKernel_range_baseChange b a)).hom ≫ _ = _
  rw [KernelRepresentative.iso_hom_comp, kernelBaseChangeIso_hom_ι]

/-- The centralizer of the full character kernel commutes with arbitrary base
change as a subgroup functor on every scheme test. -/
theorem kernelCentralizer_baseChange (i : S.toGrp ⟶ G) (a : characterLattice S) :
    kernelCentralizer ((GroupScheme.baseChange b).map i)
        (characterLattice.baseChange b S a) =
      (kernelCentralizer i a).baseChange b := by
  rw [kernelCentralizer_eq_torusCentralizer, kernelCentralizer_eq_torusCentralizer,
    ← torusCentralizer_baseChange]
  exact (torusCentralizer_eq_of_iso
    (A := (CommGroupScheme.baseChange b).obj (characterKernelComm a))
    (B := characterKernelComm (characterLattice.baseChange b S a))
    ((GroupScheme.baseChange b).map (characterKernelι a ≫ i))
    (characterKernelι (characterLattice.baseChange b S a) ≫
      (GroupScheme.baseChange b).map i)
    (characterKernelBaseChangeIso b a)
    (by rw [← Category.assoc, characterKernelBaseChangeIso_hom_ι,
      Functor.map_comp])).symm

/-- A supplied representative of the full-kernel centralizer remains a
representative after arbitrary base change. -/
theorem kernelCentralizer_isRepresentedBy_baseChange
    (i : S.toGrp ⟶ G) (a : characterLattice S) {j : C ⟶ G}
    (hj : (kernelCentralizer i a).IsRepresentedBy j) :
    (kernelCentralizer ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b S a)).IsRepresentedBy
        ((GroupScheme.baseChange b).map j) := by
  rw [kernelCentralizer_baseChange]
  exact hj.baseChange b

end Langlands.GroupScheme.RelativeRoot
