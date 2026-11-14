import Langlands.GroupScheme.Rational.SmoothKernelCentralizerQuotient
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Radicals of full character-kernel centralizer components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TrivialTarget

variable {k : Type u} [Field k]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [LocallyOfFiniteType Q.X.hom]
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    {r : U ⟶ G}

/-- A represented radical is killed by a flat scheme-surjective map to an
affine finite-type group with trivial ground-field radical. -/
theorem IsUnipotentRadical.range_le_kernel_of_trivial_target
    (hr : IsUnipotentRadical r) (hQ : HasTrivialUnipotentRadical Q) :
    SubgroupFunctor.range r ≤ SubgroupFunctor.range (kernelι q) := by
  have hle := HasSmoothConnectedUnipotentKernel.radical_le_comap (q := q) hr
    (isUnipotentRadical_kernelUnit Q hQ)
  rw [range_kernelUnit] at hle
  intro X x hx
  apply (mem_range_kernelι_iff q x).mpr
  have h := hle X hx
  simpa only [SubgroupFunctor.mem_comap, SubgroupFunctor.bot_carrier,
    Subgroup.mem_bot] using h

end TrivialTarget

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H C E : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth E.X.hom] [IsAffineHom E.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hq : Smooth q.hom.hom.left) (hH : IsConnectedReductive H)
    {jC : C ⟶ G} {jE : E ⟶ H}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hE : (kernelCentralizer (i ≫ q) a).IsRepresentedBy jE)
    (hjE : IsClosedSubgroup jE)
    {U : GroupScheme (Spec (CommRingCat.of k))}
    {r : U ⟶ identityComponent C}
    (hr : IsUnipotentRadical r)

include hS ha hq hH hC hE hjE hr

/-- The component radical maps into the full scheme-theoretic ambient kernel.
Only the target ambient group is assumed reductive. -/
theorem kernelCentralizerIdentity_radical_le_kernel :
    SubgroupFunctor.range (r ≫ (identityComponentι C ≫ jC)) ≤
      SubgroupFunctor.range (kernelι q) := by
  let p := kernelCentralizerIdentityMap i a q hC hE
  have hp := kernelCentralizerIdentityMap_smooth_surjective i a q hS hq hC hE
  have : Smooth p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2
  have hEred : IsConnectedReductive (identityComponent E) :=
    kernelCentralizerComponentReductive k H hH S hS (i ≫ q) a ha E jE hE hjE
      inferInstance
  have hle := hr.range_le_kernel_of_trivial_target p hEred.hasTrivialUnipotentRadical
  intro X x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply (mem_range_kernelι_iff q _).mpr
  have hy : (y ≫ r.hom.hom) ≫ p.hom.hom = 1 :=
    (mem_range_kernelι_iff p _).mp
      (hle X (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
  have hs := congrArg (fun f : identityComponent C ⟶ H => f.hom.hom)
    (kernelCentralizerIdentityMap_comp_ambient i a q hC hE)
  change (y ≫ r.hom.hom ≫ (identityComponentι C ≫ jC).hom.hom) ≫
    q.hom.hom = 1
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← hs]
  simp only [Grp.comp_hom_hom]
  rw [← Category.assoc, ← Category.assoc, hy, MonObj.one_comp]

variable {N : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G)
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n)

include hk

/-- With a supplied representative of the ambient kernel, the component
radical has its actual ambient image in that representative. -/
theorem kernelCentralizerIdentity_radical_le_ambient :
    SubgroupFunctor.range (r ≫ (identityComponentι C ≫ jC)) ≤
      SubgroupFunctor.range n := by
  rw [← hk]
  exact kernelCentralizerIdentity_radical_le_kernel i a q hS ha hq hH hC hE hjE hr

/-- An ambient nonradical point of the component is nonradical internally. -/
theorem kernelCentralizerIdentity_not_mem_radical
    {X : Over (Spec (CommRingCat.of k))} (x : X ⟶ (identityComponent C).X)
    (hx : x ≫ (identityComponentι C ≫ jC).hom.hom ∉
      (SubgroupFunctor.range n).carrier X) :
    x ∉ (SubgroupFunctor.range r).carrier X := by
  intro hxr
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hxr
  apply hx
  apply kernelCentralizerIdentity_radical_le_ambient i a q hS ha hq hH hC hE hjE hr
    n hk X
  exact SubgroupFunctor.mem_range.mpr ⟨y, by simp only [Grp.comp_hom_hom, Category.assoc]⟩

variable (hn : IsUnipotentRadical n)

/-- The actual homomorphism from the represented component radical into the
represented ambient radical, obtained from the proved all-test containment. -/
def kernelCentralizerRadicalMap : U ⟶ N := by
  have : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  have : Mono r.hom.hom := Over.mono_of_mono_left _
  have : Mono jC.hom.hom := hC.1
  have : Mono (r ≫ (identityComponentι C ≫ jC)).hom.hom := by
    change Mono (r.hom.hom ≫ (identityComponentι C).hom.hom ≫ jC.hom.hom)
    infer_instance
  have : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  have : Mono n.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.factorOfRangeLE
    (kernelCentralizerIdentity_radical_le_ambient i a q hS ha hq hH hC hE hjE hr n hk)

@[reassoc]
theorem kernelCentralizerRadicalMap_comp :
    kernelCentralizerRadicalMap i a q hS ha hq hH hC hE hjE hr n hk hn ≫ n =
      r ≫ (identityComponentι C ≫ jC) := by
  have : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  have : Mono r.hom.hom := Over.mono_of_mono_left _
  have : Mono jC.hom.hom := hC.1
  have : Mono (r ≫ (identityComponentι C ≫ jC)).hom.hom := by
    change Mono (r.hom.hom ≫ (identityComponentι C).hom.hom ≫ jC.hom.hom)
    infer_instance
  have : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  have : Mono n.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.factorOfRangeLE_comp
    (kernelCentralizerIdentity_radical_le_ambient i a q hS ha hq hH hC hE hjE hr n hk)

end RelativeRoot

end Langlands.GroupScheme
