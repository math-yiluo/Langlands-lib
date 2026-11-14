import Langlands.GroupScheme.Rational.SmoothKernelCentralizerQuotient
import Langlands.GroupScheme.Rational.EnvelopeKernelGeometry
import Langlands.GroupScheme.RepresentedActionFixed
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Rational.SplitUnipotentSolvable
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient

/-! # The full kernel of a character-kernel centralizer quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AutomorphicAction

/-- Every full scheme-theoretic kernel is invariant under conjugation. -/
theorem conjugation_kernel_isStable {B : Scheme.{u}} {T G H : GroupScheme B}
    (i : T ⟶ G) (q : G ⟶ H) :
    (conjugation i).IsStable (SubgroupFunctor.range (kernelι q)) := by
  intro X s x hx
  apply (mem_range_kernelι_iff q _).mpr
  have hxq := (mem_range_kernelι_iff q x).mp hx
  simp only [conjugation_act, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, hxq, mul_one, mul_inv_cancel]

end AutomorphicAction

namespace RelativeRoot

section FullKernel

variable {k : Type u} [Field k] [PerfectField k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    (hS : IsSplitTorus S.toGrp)
    (hq : HasSmoothConnectedUnipotentKernel q)
    {jC : C ⟶ G}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hjC : IsClosedSubgroup jC)

include hS hq hC hjC

/-- The full kernel of the restriction to the full character-kernel centralizer
is smooth, connected and unipotent. The character can be nonprimitive or zero. -/
theorem kernelCentralizerMap_fullKernel_geometry :
    HasSmoothConnectedUnipotentKernel (jC ≫ q) := by
  have : Smooth (kernel q).X.hom := hq.1
  have : ConnectedSpace (kernel q).X.left := hq.2.1
  have : IsAffineHom (kernel q).X.hom := by
    rw [← (kernelι q).hom.hom.w]
    infer_instance
  have hNsolv : IsSolvableScheme (kernel q) :=
    (perfectFieldUnipotentSplit k (kernel q) hq.2.1 hq.2.2).isSolvableScheme
  let c := (AutomorphicAction.conjugation i).onRepresentedSubgroup (kernelι q)
    (show (SubgroupFunctor.range (kernelι q)).IsRepresentedBy (kernelι q) from
      ⟨inferInstance, rfl⟩)
    (AutomorphicAction.conjugation_kernel_isStable i q)
  let t := SectionedSubgroupKernel.toAmbientKernel jC (kernelι q) q rfl
  have htcl : IsClosedSubgroup t :=
    SectionedSubgroupKernel.closed_toAmbientKernel jC (kernelι q) q rfl hjC
      (inferInstanceAs (IsClosedImmersion (kernelι q).hom.hom.left))
  have htmono : Mono t.hom.hom := by
    have : IsClosedImmersion t.hom.hom.left := htcl
    exact Over.mono_of_mono_left _
  have ht :
      (c.restrict (characterKernelι a)).fixedSubgroup.IsRepresentedBy t := by
    refine ⟨htmono, ?_⟩
    change SubgroupFunctor.range
      (SectionedSubgroupKernel.toAmbientKernel jC (kernelι q) q rfl) = _
    rw [SectionedSubgroupKernel.range_toAmbientKernel, hC.2]
    exact (AutomorphicAction.onRepresentedSubgroup_restrict_fixedSubgroup_eq_comap
      (AutomorphicAction.conjugation i) (kernelι q)
      ⟨inferInstance, rfl⟩ (AutomorphicAction.conjugation_kernel_isStable i q)
      (characterKernelι a)).symm
  have : AddGroup.FG (Diagonalizable.quotientLattice a) :=
    Diagonalizable.quotientLattice_fg S hS a
  have hKs : Smooth (kernel (jC ≫ q)).X.hom :=
    Diagonalizable.fixedSubgroup_smooth_of_actingIso
      Diagonalizable.FixedSmooth.fixedSubgroupSmooth
      (c.restrict (characterKernelι a)) (Diagonalizable.kernelDiagonalizableIso S hS a)
      inferInstance inferInstance t ht htcl
  have hcontains : c.fixedSubgroup ≤ (c.restrict (characterKernelι a)).fixedSubgroup := by
    intro X x hx V b s
    simpa only [AutomorphicAction.restrict_act] using
      hx V b (s ≫ (characterKernelι a).hom.hom)
  have hKc : ConnectedSpace (kernel (jC ≫ q)).X.left :=
    Torus.solvableFixedContainmentConnected k (kernel q)
      inferInstance inferInstance inferInstance hNsolv S hS c
      (c.restrict (characterKernelι a)).fixedSubgroup
      (c.fixed_restrict_isStable (characterKernelι a)) hcontains
      (kernel (jC ≫ q)) t ht htcl hKs
  exact ⟨hKs, hKc,
    unipotentClosedSubgroup k (kernel q) (kernel (jC ≫ q)) t htcl hq.2.2⟩

end FullKernel

section IdentityKernel

variable {k : Type u} [Field k] [PerfectField k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H C E : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth E.X.hom] [IsAffineHom E.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    (hS : IsSplitTorus S.toGrp)
    (hq : HasSmoothConnectedUnipotentKernel q)
    {jC : C ⟶ G} {jE : E ⟶ H}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hE : (kernelCentralizer (i ≫ q) a).IsRepresentedBy jE)
    (hjC : IsClosedSubgroup jC)

include hS hq hC hE hjC

/-- The full kernel of the actual identity-component restriction is smooth,
connected and unipotent over the original perfect field. -/
theorem kernelCentralizerIdentityMap_kernel_geometry :
    HasSmoothConnectedUnipotentKernel (kernelCentralizerIdentityMap i a q hC hE) := by
  let p := kernelCentralizerIdentityMap i a q hC hE
  have hK := kernelCentralizerMap_fullKernel_geometry i a q hS hq hC hjC
  have : Smooth (kernel (jC ≫ q)).X.hom := hK.1
  have : ConnectedSpace (kernel (jC ≫ q)).X.left := hK.2.1
  let f := IdentityComponent.factor C (kernelι (jC ≫ q))
  have hf : f ≫ identityComponentι C = kernelι (jC ≫ q) :=
    IdentityComponent.factor_identityComponentι C _
  have hfclosed : IsClosedSubgroup f := by
    apply IsClosedSubgroup.of_comp (IdentityComponent.isClosedSubgroup_identityComponentι C)
    rw [hf]
    exact inferInstanceAs (IsClosedImmersion (kernelι (jC ≫ q)).hom.hom.left)
  have : IsClosedImmersion f.hom.hom.left := hfclosed
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : Mono jE.hom.hom := hE.1
  have : Mono (identityComponentι E ≫ jE).hom.hom := by
    change Mono ((identityComponentι E).hom.hom ≫ jE.hom.hom)
    infer_instance
  have hpoint (X : Over (Spec (CommRingCat.of k)))
      (x : X ⟶ (identityComponent C).X) :
      x ≫ p.hom.hom = 1 ↔
        (x ≫ (identityComponentι C).hom.hom) ≫ (jC ≫ q).hom.hom = 1 := by
    have he :
        (x ≫ p.hom.hom) ≫ (identityComponentι E ≫ jE).hom.hom =
          (x ≫ (identityComponentι C).hom.hom) ≫ (jC ≫ q).hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun g : identityComponent C ⟶ H => x ≫ g.hom.hom)
          (kernelCentralizerIdentityMap_comp_ambient i a q hC hE)
    constructor
    · intro hx
      rw [← he, hx, MonObj.one_comp]
    · intro hx
      apply (cancel_mono (identityComponentι E ≫ jE).hom.hom).mp
      rw [he, hx, MonObj.one_comp]
  have hker : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range f := by
    ext X x
    rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range, hpoint]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
        ((mem_range_kernelι_iff (jC ≫ q) _).mpr hx)
      refine ⟨y, (cancel_mono (identityComponentι C).hom.hom).mp ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hf]
      exact hy
    · rintro ⟨y, rfl⟩
      rw [Category.assoc y f.hom.hom (identityComponentι C).hom.hom,
        ← Grp.comp_hom_hom, hf]
      exact (kernelPointsEquiv (jC ≫ q) X y).property
  exact ⟨KernelRepresentative.smooth p f hker,
    KernelRepresentative.connectedSpace p f hker,
    KernelRepresentative.isUnipotent p f hker hK.2.2⟩

/-- The actual identity-component restriction with its smooth surjectivity and
full smooth connected unipotent kernel. -/
def kernelCentralizerIdentityQuotient
    [Smooth G.X.hom] [Smooth H.X.hom] (hqs : Smooth q.hom.hom.left) :
    {p : identityComponent C ⟶ identityComponent E //
      Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
        HasSmoothConnectedUnipotentKernel p} :=
  ⟨kernelCentralizerIdentityMap i a q hC hE,
    (kernelCentralizerIdentityMap_smooth_surjective i a q hS hqs hC hE).1,
    (kernelCentralizerIdentityMap_smooth_surjective i a q hS hqs hC hE).2,
    kernelCentralizerIdentityMap_kernel_geometry i a q hS hq hC hE hjC⟩

end IdentityKernel

end RelativeRoot
end Langlands.GroupScheme
