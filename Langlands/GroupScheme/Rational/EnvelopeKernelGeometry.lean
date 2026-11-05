import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.GroupScheme.Lie.SurjectiveDifferentialLifting
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof

/-! # Kernels of sectioned subgroups and torus envelopes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SectionedSubgroupKernel

section Base

variable {S : Scheme.{u}} {H G N Q : GroupScheme S}
    (h : H ⟶ G) (n : N ⟶ G) (q : G ⟶ Q)

/-- The restricted full kernel maps into the ambient full kernel on every test. -/
theorem range_le_kernel :
    SubgroupFunctor.range (kernelι (h ≫ q) ≫ h) ≤
      SubgroupFunctor.range (kernelι q) := by
  rintro T x ⟨y, rfl⟩
  apply (mem_range_kernelι_iff q _).mpr
  change (y ≫ (kernelι (h ≫ q)).hom.hom) ≫ (h ≫ q).hom.hom = 1
  exact (kernelPointsEquiv (h ≫ q) T y).property

/-- The actual restricted kernel, viewed inside any monomorphic representative
of the full ambient kernel. -/
def toAmbientKernel [Mono n.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    kernel (h ≫ q) ⟶ N :=
  (show (SubgroupFunctor.range n).IsRepresentedBy n from ⟨inferInstance, rfl⟩).factorHom
    (kernelι (h ≫ q) ≫ h) (by
      rw [← hker]
      exact range_le_kernel h q)

@[reassoc]
theorem toAmbientKernel_comp [Mono n.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    toAmbientKernel h n q hker ≫ n = kernelι (h ≫ q) ≫ h :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The kernel inside the ambient kernel is exactly the inverse image of the
subgroup, on arbitrary relative test schemes. -/
theorem range_toAmbientKernel [Mono n.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    SubgroupFunctor.range (toAmbientKernel h n q hker) =
      (SubgroupFunctor.range h).comap n := by
  ext T x
  change (∃ y : T ⟶ (kernel (h ≫ q)).X,
      y ≫ (toAmbientKernel h n q hker).hom.hom = x) ↔
    ∃ y : T ⟶ H.X, y ≫ h.hom.hom = x ≫ n.hom.hom
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (kernelι (h ≫ q)).hom.hom, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => y ≫ f.hom.hom) (toAmbientKernel_comp h n q hker).symm
  · rintro ⟨y, hy⟩
    have hx : (x ≫ n.hom.hom) ≫ q.hom.hom = 1 := by
      apply (mem_range_kernelι_iff q _).mp
      rw [hker]
      exact ⟨x, rfl⟩
    have hyq : y ≫ (h ≫ q).hom.hom = 1 := by
      rw [Grp.comp_hom_hom, ← Category.assoc, hy, hx]
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp
      ((mem_range_kernelι_iff (h ≫ q) y).mpr hyq)
    refine ⟨z, (cancel_mono n.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, toAmbientKernel_comp,
      Grp.comp_hom_hom, ← Category.assoc, hz, hy]

/-- The restricted kernel is closed inside the ambient kernel. -/
theorem closed_toAmbientKernel [Mono n.hom.hom] [IsSeparated Q.X.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n)
    (hh : IsClosedSubgroup h) (hn : IsClosedSubgroup n) :
    IsClosedSubgroup (toAmbientKernel h n q hker) := by
  apply IsClosedSubgroup.of_comp hn
  rw [toAmbientKernel_comp]
  exact (show IsClosedSubgroup (kernelι (h ≫ q)) from
    inferInstanceAs (IsClosedImmersion (kernelι (h ≫ q)).hom.hom.left)).comp hh

end Base

section Field

variable {k : Type u} [Field k]
    {H G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType Q.X.hom]
    (h : H ⟶ G) (q : G ⟶ Q) (sH : Q ⟶ H)
    (hs : sH ≫ (h ≫ q) = 𝟙 Q)

include sH hs in
omit [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType Q.X.hom] in
/-- A homomorphic section makes the actual quotient differential surjective. -/
theorem differential_surjective :
    Function.Surjective (Lie.targetMapLinear (h ≫ q) k) := by
  intro x
  refine ⟨Lie.targetMapLinear sH k x, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  change (x.toMul.val ≫ sH.hom.hom) ≫ (h ≫ q).hom.hom = x.toMul.val
  rw [Category.assoc, ← Grp.comp_hom_hom, hs, Grp.id_hom_hom, Category.comp_id]

include sH hs in
/-- A sectioned homomorphism from a smooth affine group is smooth. -/
theorem smooth_projection [Smooth H.X.hom] :
    Smooth (h ≫ q).hom.hom.left :=
  Lie.smooth_of_surjective_differential (h ≫ q) inferInstance
    (differential_surjective h q sH hs)

include sH hs in
/-- The restriction is an fppf quotient by its full scheme-theoretic kernel. -/
theorem isFppfQuotient [Smooth H.X.hom] :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι (h ≫ q))) (h ≫ q) := by
  have : Smooth (h ≫ q).hom.hom.left := smooth_projection h q sH hs
  have hs' : sH.hom.hom.left ≫ (h ≫ q).hom.hom.left = 𝟙 Q.X.left :=
    congrArg (fun f => f.hom.hom.left) hs
  have hsurj : Surjective (h ≫ q).hom.hom.left := by
    constructor
    intro x
    refine ⟨sH.hom.hom.left x, ?_⟩
    change (sH.hom.hom.left ≫ (h ≫ q).hom.hom.left) x = x
    rw [hs']
    rfl
  exact ⟨inferInstance, hsurj, inferInstance, rfl⟩

include sH hs in
omit [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType Q.X.hom] in
/-- The full restricted kernel is smooth and connected. -/
theorem smooth_connected [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    Smooth (kernel (h ≫ q)).X.hom ∧ ConnectedSpace (kernel (h ≫ q)).X.left :=
  SplitKernelRetract.smooth_connected_kernel (h ≫ q) (𝟙 Q) (h ≫ q) sH
    (Category.comp_id _) hs

end Field

section Unipotent

variable {k : Type u} [Field k]
    {H G N Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [IsAffineHom Q.X.hom]
    [LocallyOfFiniteType N.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (h : H ⟶ G) (n : N ⟶ G) (q : G ⟶ Q)
    [Mono n.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n)
    (hh : IsClosedSubgroup h) (hn : IsClosedSubgroup n)
    (sH : Q ⟶ H) (hs : sH ≫ (h ≫ q) = 𝟙 Q)

omit [Smooth H.X.hom] [ConnectedSpace H.X.left] in
/-- Affineness of the restricted kernel follows from its closed inclusion. -/
theorem isAffineHom : IsAffineHom (kernel (h ≫ q)).X.hom := by
  rw [← (kernelι (h ≫ q)).hom.hom.w]
  infer_instance

include n hker hh hn in
omit [IsAffineHom H.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left] in
/-- A closed restricted kernel of a unipotent ambient kernel is unipotent. -/
theorem isUnipotent (hN : IsUnipotent N) : IsUnipotent (kernel (h ≫ q)) :=
  unipotentClosedSubgroup k N (kernel (h ≫ q))
    (toAmbientKernel h n q hker) (closed_toAmbientKernel h n q hker hh hn) hN

include n hker hh hn sH hs in
/-- Over a perfect field the same actual restricted kernel has a finite split series. -/
theorem isSplitUnipotent [PerfectField k] (hN : IsUnipotent N) :
    RelativeRoot.IsSplitUnipotent (kernel (h ≫ q)) := by
  have : IsAffineHom (kernel (h ≫ q)).X.hom := isAffineHom h q
  have hgeom := smooth_connected h q sH hs
  have : Smooth (kernel (h ≫ q)).X.hom := hgeom.1
  exact perfectFieldUnipotentSplit k (kernel (h ≫ q)) hgeom.2
    (isUnipotent h n q hker hh hn hN)

end Unipotent

end SectionedSubgroupKernel

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (D : TorusGeneratedEnvelope G)
    {Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ Q.toGrp) (s : Q.toGrp ⟶ G)
    (hQ : IsTorus Q.toGrp) (hsclosed : IsClosedSubgroup s)
    (hs : s ≫ q = 𝟙 Q.toGrp)

include hs in
/-- A torus section lifts to the unchanged closed torus envelope as a section. -/
theorem torusFactor_section :
    D.torusFactor s hQ hsclosed ≫ (D.inclusion ≫ q) = 𝟙 Q.toGrp := by
  rw [← Category.assoc, D.torusFactor_comp, hs]

end TorusGeneratedEnvelope

end Langlands.GroupScheme
