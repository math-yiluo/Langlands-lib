import Langlands.GroupScheme.Rational.RelativeWeylQuotientStatement
import Langlands.GroupScheme.Rational.RelativeWeylAbsoluteRestrictionProof
import Langlands.GroupScheme.Rational.RelativeWeylGroupRestrictProof

/-! # The restriction quotient of the Weyl group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem exists_quotient_restriction
    {N A B W Q : Type*} [Group N] [Group A] [Group B] [Group W] [Group Q]
    (p : N →* A) (q : N →* B) (f : B ≃* Q) (g : W →* Q)
    (hg : Function.Bijective g) (hker : p.ker ≤ q.ker) (hq : Function.Surjective q) :
    ∃ r : p.range →* W, Function.Surjective r ∧
      g.comp (r.comp p.rangeRestrict) = f.toMonoidHom.comp q := by
  let e := MulEquiv.ofBijective g hg
  let compare := f.trans e.symm
  have hker' : p.rangeRestrict.ker ≤ q.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let lift : {q' : N →* B // p.rangeRestrict.ker ≤ q'.ker} ≃ (p.range →* B) :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective
  let descend := lift ⟨q, hker'⟩
  have hdescend : descend.comp p.rangeRestrict = q :=
    congrArg Subtype.val (lift.symm_apply_apply ⟨q, hker'⟩)
  have hsurj : Function.Surjective descend := by
    intro w
    obtain ⟨n, hn⟩ := hq w
    exact ⟨p.rangeRestrict n, (DFunLike.congr_fun hdescend n).trans hn⟩
  refine ⟨compare.toMonoidHom.comp descend, compare.surjective.comp hsurj, ?_⟩
  apply MonoidHom.ext
  intro n
  have hn : descend (p.rangeRestrict n) = q n := DFunLike.congr_fun hdescend n
  change e (compare (descend (p.rangeRestrict n))) = f (q n)
  rw [hn]
  exact e.apply_symm_apply _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Quotient classes of simultaneous normalizers restrict onto the ground-field
relative Weyl group. -/
theorem relativeWeylQuotient : RelativeWeylQuotientStatement.{u} := by
  intro k K _ _ _ G hG S i hi b iK T j f hj hf normalizers toT toS
  have : IsClosedImmersion iK.hom.hom.left := hi.1.2.baseChange b
  let U := Over.mk b
  have hConnected : ConnectedSpace U.left := by
    change ConnectedSpace (Spec (CommRingCat.of K))
    infer_instance
  refine exists_quotient_restriction toT toS (fibreRelativeWeylGroupEquiv b i)
    (relativeWeylGroupRestrict i U) (relativeWeylGroupRestrict_bijective k G hG S i hi U)
    ?_ ?_
  · intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    change (QuotientGroup.mk ⟨n.val, n.2.2⟩ : relativeWeylGroup j) = 1 at hn
    change (QuotientGroup.mk ⟨n.val, n.2.1⟩ :
      relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj S) iK) = 1
    rw [QuotientGroup.eq_one_iff] at hn ⊢
    have hT : j ≫ (((baseChange b).obj G).innerIso n.val).hom = j :=
      (mem_centralizerPoints j).mp hn
    apply (mem_centralizerPoints (T := (CommGroupScheme.baseChange b).obj S) iK).mpr
    change iK ≫ (((baseChange b).obj G).innerIso n.val).hom = iK
    rw [← hf, Category.assoc, hT]
  · have hfactor := (relativeWeylAbsoluteRestriction k K G hG S i hi T j f hj hf).1
    intro w
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨m, hm, z, hz, h⟩ := hfactor n.val n.property
    refine ⟨⟨m, hm⟩, ?_⟩
    change QuotientGroup.mk ⟨m, hm.1⟩ = QuotientGroup.mk n
    rw [QuotientGroup.eq]
    change m⁻¹ * n.val ∈ centralizerPoints (T := (CommGroupScheme.baseChange b).obj S) iK
    rw [h, inv_mul_cancel_left]
    exact hz

end Langlands.GroupScheme
