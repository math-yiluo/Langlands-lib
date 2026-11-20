import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-! # Permutations of pairwise unlinked real standard parameters -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean InductionStages

private theorem linked_symm {a b : MoeglinDatum} (h : a.IsLinked b) : b.IsLinked a := by
  rcases a with ⟨p, s⟩ | ⟨p, s⟩ <;> rcases b with ⟨q, t⟩ | ⟨q, t⟩
  · obtain ⟨k, hk, he, ⟨j, hj⟩⟩ := h
    refine ⟨-k, neg_ne_zero.mpr hk, ?_, ⟨(p.val : ℤ) + q.val - j - 1, ?_⟩⟩
    · push_cast
      linear_combination -he
    · omega
  · exact h
  · exact h
  · obtain ⟨k, hk, he⟩ := h
    have habs : ((q : ℤ) - p).natAbs = ((p : ℤ) - q).natAbs := by
      rw [show (q : ℤ) - p = -((p : ℤ) - q) by ring, Int.natAbs_neg]
    refine ⟨k, hk, ?_⟩
    simpa only [habs, or_comm] using he

private theorem unlinked_symm {a b : RealBlock} (h : AreRealBlocksUnlinked a b) :
    AreRealBlocksUnlinked b a :=
  fun c hc d hd hcd => h d hd c hc (linked_symm hcd)

private theorem has_inverse_intertwiner {n : ℕ} {ds es : List RealBlock}
    {T : KFin n ds →ₗ[ℂ] KFin n es}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T)
    (hbij : Function.Bijective T) : RealInjectiveIntertwinerExists n es ds := by
  let E := LinearEquiv.ofBijective T hbij
  refine ⟨E.symm.toLinearMap, E.symm.injective, isRealStandardIntertwiner_iff.mpr ?_⟩
  obtain ⟨hK, hL⟩ := isRealStandardIntertwiner_iff.mp hT
  constructor
  · intro k f
    apply E.injective
    change E (E.symm (kRep n es k f)) = E (kRep n ds k (E.symm f))
    rw [E.apply_symm_apply]
    change kRep n es k f = T (kRep n ds k (E.symm f))
    rw [hK]
    exact congrArg (kRep n es k) (E.apply_symm_apply f).symm
  · intro X f
    apply E.injective
    change E (E.symm (lie n es X f)) = E (lie n ds X (E.symm f))
    rw [E.apply_symm_apply]
    change lie n es X f = T (lie n ds X (E.symm f))
    rw [hL]
    exact congrArg (lie n es X) (E.apply_symm_apply f).symm

private theorem swap_unlinked (n : ℕ) (pre post : List RealBlock) (a b : RealBlock)
    (hrank : realRank (pre ++ a :: b :: post) = n) (hab : AreRealBlocksUnlinked a b) :
    RealInjectiveIntertwinerExists n (pre ++ a :: b :: post) (pre ++ b :: a :: post) := by
  rcases le_total (realBlockExponent b) (realBlockExponent a) with h | h
  · exact realUnlinkedSwap n pre post a b hrank h hab
  · have hrank' := (realRank_perm (List.Perm.append_left pre (List.Perm.swap a b post))).trans hrank
    obtain ⟨T, hTi, hT⟩ := realUnlinkedSwap n pre post b a hrank' h (unlinked_symm hab)
    exact has_inverse_intertwiner hT
      ⟨hTi, realSwapInjectiveIntertwinerSurjective n pre post b a T hrank' hTi hT⟩

private theorem perm_in_context {ds es : List RealBlock} (hp : ds.Perm es) (n : ℕ) :
    ∀ pre post : List RealBlock, realRank (pre ++ ds ++ post) = n →
      ds.Pairwise AreRealBlocksUnlinked →
      RealInjectiveIntertwinerExists n (pre ++ ds ++ post) (pre ++ es ++ post) := by
  induction hp with
  | nil =>
    intro pre post _ _
    exact RealInjectiveIntertwinerExists.refl n _
  | cons a _ ih =>
    intro pre post hrank hu
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) post
        (by simpa only [List.append_assoc, List.singleton_append] using hrank)
        (List.pairwise_cons.mp hu).2
  | swap a b tail =>
    intro pre post hrank hu
    simpa only [List.append_assoc, List.cons_append] using
      swap_unlinked n pre (tail ++ post) b a
        (by simpa only [List.append_assoc, List.cons_append] using hrank)
        ((List.pairwise_cons.mp hu).1 a (List.mem_cons_self))
  | trans hp hp' ih ih' =>
    intro pre post hrank hu
    have hpctx := (hp.append_left pre).append_right post
    have hrank' := (realRank_perm hpctx).symm.trans hrank
    exact (ih pre post hrank hu).trans (ih' pre post hrank' (hp.pairwise hu unlinked_symm))

/-- Two permutations of pairwise unlinked real blocks of total rank `n` have an injective
standard intertwiner. The exponents may be in either order. -/
def RealUnlinkedStandardPermutationStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n →
    ds.Pairwise AreRealBlocksUnlinked → ds.Perm es →
    RealInjectiveIntertwinerExists n ds es

theorem realUnlinkedStandardPermutation : RealUnlinkedStandardPermutationStatement := by
  intro n ds es hrank hu hp
  simpa only [List.nil_append, List.append_nil] using
    perm_in_context hp n [] [] (by simpa only [List.nil_append, List.append_nil] using hrank) hu

end Langlands.Archimedean
