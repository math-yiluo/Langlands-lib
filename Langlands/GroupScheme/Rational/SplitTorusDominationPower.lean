import Langlands.GroupScheme.Rational.SplitTorusDominationReduction
import Langlands.GroupScheme.Rational.UnipotentTorsionCenter
import Langlands.GroupScheme.Lie.QuotientConnectedKernelDimension
import Langlands.GroupScheme.Rational.VectorGroupSplit

/-! # Reduction of commutative domination to groups killed by a prime -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

/-- Every fppf quotient of a commutative group is commutative. The projection
is assumed quasi-compact so its product is an fpqc epimorphism. -/
theorem IsFppfQuotient.isCommMonObj
    {B : Scheme.{u}} {G Q : GroupScheme B} [IsCommMonObj G.X]
    {F : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : IsFppfQuotient F q) [QuasiCompact q.hom.hom.left] :
    IsCommMonObj Q.X := by
  apply hq.isCommMonObj_of_containsCommutators
  intro T x y
  have h : x * y * x⁻¹ * y⁻¹ = 1 := by
    simp [mul_assoc]
  rw [h]
  exact (F.carrier T).one_mem

end RelativeRoot

variable {k : Type u} [Field k]

/-- It suffices in positive characteristic to split the dominated commutative
unipotent groups killed by the characteristic prime. A last nontrivial power
image supplies a smooth connected dominated subgroup killed by that prime;
the quotient has smaller Lie dimension. -/
theorem commutative_splitUnipotent_of_splitTorusDomination_of_primeExponent
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (helem : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
      [IsCommMonObj H.X], IsUnipotent H → HasUniformPowerExponent H p →
        HasPointedSplitTorusDomination H → RelativeRoot.IsSplitUnipotent H)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsCommMonObj G.X]
    (hU : IsUnipotent G) (hG : HasPointedSplitTorusDomination G) :
    RelativeRoot.IsSplitUnipotent G := by
  classical
  refine smoothConnectedAffineGroup_lieDimension_induction
    (fun H => IsCommMonObj H.X → IsUnipotent H →
      HasPointedSplitTorusDomination H → RelativeRoot.IsSplitUnipotent H)
    ?_ G inferInstance hU hG
  intro H _ _ _ ih hHcomm hHu hHd
  let : IsCommMonObj H.X := hHcomm
  let : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  by_cases ht : SubgroupFunctor.range (𝟙 H) = ⊥
  · exact ⟨0, ht⟩
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hHu
  obtain ⟨n, hn, hn'⟩ := PowerImage.exists_last_nontrivial_multiplication p ht ⟨r, hr⟩
  let f := (multiplication H (p ^ n : ℕ)).hom.hom
  have hInt := smoothConnectedAffineGeometry.1 k H
    inferInstance inferInstance inferInstance
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k H
    inferInstance inferInstance H.X inferInstance inferInstance hInt 1 f
    (MonObj.one_comp f)
  let : Smooth D.group.X.hom := hD.1
  let : IsAffineHom D.group.X.hom := hD.2.1
  let : GeometricallyConnected D.group.X.hom := hD.2.2.1
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let : Mono D.inclusion.hom.hom := D.represents.1
  let : IsCommMonObj D.group.X := by
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro T
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (cancel_mono D.inclusion.hom.hom).1
    simp only [MonObj.mul_comp]
    exact mul_comm _ _
  have hnt : SubgroupFunctor.range D.inclusion ≠ ⊥ := by
    intro hzero
    have hf : f ∈ (SubgroupFunctor.range D.inclusion).carrier H.X :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, D.factor_comp⟩
    rw [hzero, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hf
    apply hn
    apply hom_ext_points
    intro T x
    change x ≫ f = x ≫ (1 : H ⟶ H).hom.hom
    rw [hf, Grp.Hom.hom_one, Mon.Hom.hom_one]
  have hDn : HasUniformPowerExponent D.group p :=
    PowerImage.GeneratedImage.hasUniformPowerExponent D p
      (PowerImage.image_killed_of_succ_eq_one p n hn')
  obtain ⟨m, hm⟩ := helem D.group
    (unipotentClosedSubgroup k H D.group D.inclusion D.closed hHu) hDn
    (hHd.generatedImage f (MonObj.one_comp f) D)
  have hnormal : (SubgroupFunctor.range D.inclusion).IsNormal := by
    intro T g x _ hx
    rw [mul_comm g x, mul_inv_cancel_right]
    exact hx
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k H D.group
    D.inclusion D.closed hnormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : ConnectedSpace Q.X.left := q.hom.hom.left.surjective.connectedSpace
    q.hom.hom.left.continuous
  let : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp q.hom.hom.left Q.X.hom
  let : QuasiCompact q.hom.hom.left := inferInstance
  let : IsCommMonObj Q.X := hq.isCommMonObj
  have hlt : Lie.dimension Q < Lie.dimension H :=
    hq.lieDimension_lt_of_nontrivial_connected_kernel
      (n := D.inclusion) ⟨inferInstance, rfl⟩ hD.1 hnt
  obtain ⟨j, hj⟩ := ih Q hlt inferInstance (hHu.of_flat_surjective q) (hHd.postcomp q)
  exact ⟨m + j, hm.of_fppfQuotient_of_field D.inclusion q D.closed inferInstance hq hj⟩

/-- Choose the represented split series supplied by the prime-exponent
reduction, keeping its elementary case as an explicit premise. -/
def splitSeriesOfPrimeExponentCase
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (helem : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
      [IsCommMonObj H.X], IsUnipotent H → HasUniformPowerExponent H p →
        HasPointedSplitTorusDomination H → RelativeRoot.IsSplitUnipotent H)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsCommMonObj G.X]
    (hU : IsUnipotent G) (hG : HasPointedSplitTorusDomination G) :
    {n : ℕ // RelativeRoot.HasSplitSeries n G} :=
  let h := commutative_splitUnipotent_of_splitTorusDomination_of_primeExponent
    p helem G hU hG
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
