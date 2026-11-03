import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.RootSubgroupSeparation

/-! # Automatic reflection and uniqueness of actual opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- A normalizing point centralizing the full kernel of a nonzero character
acts by a sign on that character. -/
theorem weylAction_eq_self_or_neg_of_mem_kernelCentralizer
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (n : normalizerPoints i)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _))) :
    weylAction i n a = a ∨ weylAction i n a = -a := by
  obtain ⟨m, hm⟩ :=
    exists_integral_difference_of_mem_kernelCentralizer i hT a ha n hc a
  have hcinv : (n⁻¹).val ∈
      (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _)) :=
    Subgroup.inv_mem _ hc
  obtain ⟨m', hm'⟩ :=
    exists_integral_difference_of_mem_kernelCentralizer i hT a ha n⁻¹ hcinv a
  have hwa : weylAction i n a = (1 - m) • a := by
    rw [sub_smul, one_smul, ← hm]
    abel
  have hwainv : weylAction i n⁻¹ a = (1 - m') • a := by
    rw [sub_smul, one_smul, ← hm']
    abel
  have hcomp : a = ((1 - m') * (1 - m)) • a := by
    calc
      a = weylAction i n (weylAction i n⁻¹ a) := by
        rw [map_inv]
        exact ((weylAction i n).apply_symm_apply a).symm
      _ = _ := by rw [hwainv, map_zsmul, hwa, smul_smul]
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have heq := congrArg (fun b => latticePairing T b ν) hcomp
  simp only [map_zsmul, LinearMap.smul_apply, hν, zsmul_eq_mul] at heq
  have hunit : (1 - m) * (1 - m') = 1 := by
    have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    have hmul : ((1 - m') * (1 - m)) * (D : ℤ) = 1 * D := by
      simpa using heq.symm
    simpa only [mul_comm (1 - m') (1 - m)] using mul_right_cancel₀ hD0 hmul
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with hsign | hsign
  · exact Or.inl (by simpa only [hsign, one_smul] using hwa)
  · exact Or.inr (by simpa only [hsign, neg_one_smul] using hwa)

namespace RelativeRoot

variable [IsAffineHom G.X.hom]
  {a : characterLattice T} {x : rationalPoints G}
  {p : rationalPoints G × rationalPoints G}

/-- A normalizing opposite pair of a nonidentity root point cannot fix its
character: moving one opposite factor past the normalizer would give a
two-factor normalizer. -/
theorem IsOppositeFactorPair.weylAction_ne_self
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) :
    weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a ≠ a := by
  intro hfix
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hfix' : weylAction i n a = a := hfix
  have hinv : weylAction i n⁻¹ a = a := by
    calc
      weylAction i n⁻¹ a = weylAction i n⁻¹ (weylAction i n a) := by rw [hfix']
      _ = a := by
        rw [map_inv]
        exact (weylAction i n).symm_apply_apply a
  have hneg : weylAction i n⁻¹ (-a) = -a := by rw [map_neg, hinv]
  have hconj := normalizer_conj_mem i (-a) n⁻¹ hp.1
  simp only [G.constantPoint_self, Subgroup.coe_inv, inv_inv, hneg] at hconj
  have hy : p.2 * (n.val⁻¹ * p.1 * n.val) ∈
      (subgroup i (-a)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ hp.2.1 hconj
  have hn1 := normalizer_eq_one_of_mul_opposite i hT ha n hx hy
    (by simp [n, mul_assoc])
  have heq : x * (p.2 * (n.val⁻¹ * p.1 * n.val)) = 1 := by
    have h := congrArg Subtype.val hn1
    simpa [n, mul_assoc] using h
  have hxopp : x ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) := by
    rw [mul_eq_one_iff_eq_inv.mp heq]
    exact Subgroup.inv_mem _ hy
  exact hx1 (eq_one_of_mem_subgroup_of_mem_opposite i hT ha hx hxopp)

/-- Every actual normalizing opposite pair of a nonidentity root point
negates the root, without a reductivity or finiteness premise. -/
theorem IsOppositeFactorPair.weylAction_eq_neg
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) :
    weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a :=
  (weylAction_eq_self_or_neg_of_mem_kernelCentralizer i hT ha
    ⟨p.1 * x * p.2, hp.2.2⟩ (hp.mem_kernelCentralizer i hx)).resolve_left
      (hp.weylAction_ne_self i hT ha hx hx1)

/-- Any two actual normalizing opposite pairs of a nonidentity root point
are equal, without supplying their Weyl actions. -/
theorem IsOppositeFactorPair.eq
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) {q : rationalPoints G × rationalPoints G}
    (hq : IsOppositeFactorPair i a x q) : p = q :=
  hp.eq_of_flip i hT ha hq (hp.weylAction_eq_neg i hT ha hx hx1)

/-- The integral coroot of an actual normalizing opposite pair of a
nonidentity root point; the root flip is proved internally. -/
def IsOppositeFactorPair.coroot
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) : cocharacterLattice T :=
  hp.corootOfFlip i hT ha hx (hp.weylAction_eq_neg i hT ha hx hx1)

/-- The actual pair coroot has self-pairing two and gives the normalizer's
reflection formula on the full integral character lattice. -/
theorem IsOppositeFactorPair.coroot_spec
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) :
    latticePairing T a (hp.coroot i hT ha hx hx1) = 2 ∧
      ∀ χ : characterLattice T,
        weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) χ =
          χ - latticePairing T χ (hp.coroot i hT ha hx hx1) • a :=
  hp.corootOfFlip_spec i hT ha hx (hp.weylAction_eq_neg i hT ha hx hx1)

/-- Every actual normalizing opposite pair of a nonidentity relative-root
point represents the exact relative reflection. -/
theorem IsOppositeFactorPair.isRelativeReflection
    (hT : IsSplitTorus T.toGrp) (ha : a ∈ relativeRoots i)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    (hp : IsOppositeFactorPair i a x p) :
    IsRelativeReflection i a
      (QuotientGroup.mk (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i)) :=
  hp.isRelativeReflection_of_flip i hT ha hx
    (hp.weylAction_eq_neg i hT ha.1 hx hx1)

end RelativeRoot

end Langlands.GroupScheme
