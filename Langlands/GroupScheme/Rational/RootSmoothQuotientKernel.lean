import Langlands.GroupScheme.Rational.RootSmoothQuotient
import Langlands.GroupScheme.Rational.SemigroupComparisonProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Split-unipotent kernels of root maps induced by unipotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot.SmoothQuotient

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G U V N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ H) (q : H ⟶ G) (a : characterLattice S) (ha : a ≠ 0)
    (j : U ⟶ H) (l : V ⟶ G)
    (hj : (subgroup i a).IsRepresentedBy j)
    (hl : (subgroup (i ≫ q) a).IsRepresentedBy l)

omit [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom] [Smooth G.X.hom] in
/-- The full kernel of the induced root map is the inverse image, in the
source root representative, of the full kernel of the ambient map. -/
theorem range_kernelι_rootMap :
    SubgroupFunctor.range (kernelι (rootMap i q a j l hj hl)) =
      (SubgroupFunctor.range (kernelι q)).comap j := by
  have : Mono l.hom.hom := hl.1
  rw [← range_kernelι_comp_mono (rootMap i q a j l hj hl) l, rootMap_comp,
    range_kernelι_comp_eq_comap]

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
include hS ha in
/-- If the full kernel of the ambient map is represented by a smooth connected
normal closed subgroup `n`, then the full kernel of the induced root map is
unipotent and split unipotent. The proof identifies it, through `n`, with a
representative of the positive cyclic semigroup subgroup of `n` for the
restricted torus action. -/
theorem rootMap_kernel_isSplitUnipotent
    (n : N ⟶ H) (hn : IsClosedSubgroup n) (hNs : Smooth N.X.hom)
    (hNc : ConnectedSpace N.X.left) (hnorm : (SubgroupFunctor.range n).IsNormal)
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    IsUnipotent (kernel (rootMap i q a j l hj hl)) ∧
      IsSplitUnipotent (kernel (rootMap i q a j l hj hl)) := by
  set p := rootMap i q a j l hj hl with hp
  let b := AutomorphicAction.conjugation i
  have : IsClosedImmersion n.hom.hom.left := hn
  have hnmono : Mono n.hom.hom := Over.mono_of_mono_left _
  have hjmono : Mono j.hom.hom := hj.1
  have hnrep : (SubgroupFunctor.range n).IsRepresentedBy n := ⟨hnmono, rfl⟩
  have hstab : b.IsStable (SubgroupFunctor.range n) := by
    intro T h g hg
    rw [AutomorphicAction.conjugation_act]
    exact hnorm T (h ≫ i.hom.hom) g trivial hg
  let c := AutomorphicAction.onRepresentedSubgroup b n hnrep hstab
  have hc : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ N.X),
      c.act s h ≫ n.hom.hom = b.act s (h ≫ n.hom.hom) := fun T s h =>
    AutomorphicAction.onRepresentedSubgroup_act_comp b n hnrep hstab s h
  have hNaff : IsAffineHom N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have hint := semigroupComparison.2.2 k H N inferInstance hNs inferInstance hNaff hNc
    S hS b c n hn hc (cyclicTail a 1) (Or.inr (Or.inr hnorm))
  have hsub : semigroupSubgroup b (cyclicTail a 1) = subgroup i a := by
    change weightFiltration (AutomorphicAction.conjugation i) a 1 = subgroup i a
    exact weightFiltration_one_eq_subgroup hS i a ha
  have hkerp : SubgroupFunctor.range (kernelι p) =
      (SubgroupFunctor.range n).comap j := by
    rw [hp, range_kernelι_rootMap i q a j l hj hl, hker]
  have hle : SubgroupFunctor.range (kernelι p ≫ j) ≤ SubgroupFunctor.range n := by
    rintro T _ ⟨x, rfl⟩
    have hx : x ≫ (kernelι p).hom.hom ∈ (SubgroupFunctor.range (kernelι p)).carrier T :=
      ⟨x, rfl⟩
    rw [hkerp, SubgroupFunctor.mem_comap] at hx
    change x ≫ (kernelι p ≫ j).hom.hom ∈ _
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hx
  let e : kernel p ⟶ N := hnrep.factorHom (kernelι p ≫ j) hle
  have he : e ≫ n = kernelι p ≫ j := hnrep.factorHom_comp _ hle
  have hrep : (semigroupSubgroup c (cyclicTail a 1)).IsRepresentedBy e := by
    refine ⟨?_, ?_⟩
    · have hcomp : Mono (e ≫ n).hom.hom := by
        rw [he, Grp.comp_hom_hom]
        infer_instance
      rw [Grp.comp_hom_hom] at hcomp
      exact mono_of_mono _ n.hom.hom
    · rw [← hint, hsub, ← hj.2]
      apply SubgroupFunctor.ext
      intro T
      apply Subgroup.ext
      intro y
      rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨z ≫ (kernelι p).hom.hom, ?_⟩
        rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, he]
      · rintro ⟨x, hx⟩
        have hxk : x ∈ (SubgroupFunctor.range (kernelι p)).carrier T := by
          rw [hkerp, SubgroupFunctor.mem_comap, hx]
          exact ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hxk
        refine ⟨z, ?_⟩
        apply (cancel_mono n.hom.hom).1
        rw [Category.assoc, ← Grp.comp_hom_hom, he, Grp.comp_hom_hom, ← Category.assoc, hz,
          hx]
  exact (semigroupRealization k N hNs hNaff S hS c (cyclicTail a 1)).2.2.2.1
    (kernel p) e hrep (fun h0 => by
      obtain ⟨m, _, hm, hma⟩ := h0
      exact hS.nsmul_ne_zero ha (Nat.ne_of_gt hm) hma)

include hS ha in
/-- With a smooth surjective ambient map, the induced root map is the actual
represented fppf quotient by its full kernel inclusion. -/
theorem rootMap_isFppfQuotient
    (hq : Smooth q.hom.hom.left) (hqs : Surjective q.hom.hom.left) :
    IsFppfQuotient (SubgroupFunctor.range (kernelι (rootMap i q a j l hj hl)))
      (rootMap i q a j l hj hl) := by
  obtain ⟨hps, hpsurj⟩ := rootMap_smooth_surjective hS i q a ha j l hj hl hq hqs
  exact ⟨inferInstance, hpsurj, inferInstance, rfl⟩

include hS ha in
/-- With a smooth surjective ambient map, the full kernel of the induced
root map is smooth. -/
theorem rootMap_kernel_smooth
    (hq : Smooth q.hom.hom.left) (hqs : Surjective q.hom.hom.left) :
    Smooth (kernel (rootMap i q a j l hj hl)).X.hom := by
  have : Smooth (rootMap i q a j l hj hl).hom.hom.left :=
    (rootMap_smooth_surjective hS i q a ha j l hj hl hq hqs).1
  exact MorphismProperty.of_isPullback (kernel_isPullback_scheme _) inferInstance

omit [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom] [Smooth G.X.hom] in
/-- The full kernel inclusion of the induced root map is closed when the
target root representative is affine. -/
theorem kernelι_rootMap_isClosedSubgroup [IsAffineHom V.X.hom] :
    IsClosedSubgroup (kernelι (rootMap i q a j l hj hl)) :=
  inferInstanceAs (IsClosedImmersion (kernelι (rootMap i q a j l hj hl)).hom.hom.left)

end Langlands.GroupScheme.RelativeRoot.SmoothQuotient
