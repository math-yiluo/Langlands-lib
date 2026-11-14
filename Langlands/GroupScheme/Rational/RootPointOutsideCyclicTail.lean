import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Rational root points outside the second cyclic weight tail -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

include hS

/-- The exact root weight prevents the root functor from lying in its
second cyclic weight tail. -/
theorem subgroup_not_le_second_cyclicTail
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ¬ subgroup i a ≤ weightFiltration (AutomorphicAction.conjugation i) a 2 := by
  intro hle
  let b := AutomorphicAction.conjugation i
  have hsupp : a ∈ actionWeightSupport b (subgroup i a) := by
    apply (HasLieImage.mem_actionWeightSupport_iff b hS (cyclicTail a 1)
      (hasLieImage_subgroup i a hS ha.1) a).mpr
    refine ⟨⟨1, by decide, by decide, one_smul ℕ a⟩, ?_⟩
    simpa only [b, actionWeightSpace_conjugation] using ha.2
  have htail := ((HasLieImage.mem_actionWeightSupport_iff b hS (cyclicTail a 2)
    (hasLieImage_semigroupSubgroup b hS (cyclicTail a 2)) a).mp
      (actionWeightSupport_mono b hle hsupp)).1
  obtain ⟨n, hn, _, he⟩ := htail
  have hn1 : n = 1 := hS.nsmul_character_injective ha.1
    (by simpa only [one_smul] using he)
  omega

/-- A nonidentity point of the first cyclic vector quotient lifts over the
original field because its actual kernel is smooth split unipotent. -/
theorem exists_rootPoint_not_mem_second_cyclicTail
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (weightFiltration (AutomorphicAction.conjugation i) a 2).carrier
          (Over.mk (𝟙 _)) := by
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    cyclicRootFunctorComparison k G inferInstance inferInstance S hS i a ha.1
  obtain ⟨H, j, hj, hjc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha.1
  have : Mono j.hom.hom := hj.1
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  obtain ⟨V, q, c, _, hq, hc, _, _⟩ :=
    (cyclicWeightFiltration k G inferInstance inferInstance S hS b a ha.1 1
      (by decide)).2 H j (hfirst.symm ▸ hj)
  change IsFppfQuotient ((weightFiltration b a 2).comap j) q at hq
  obtain ⟨n, hn⟩ := hc.isVectorGroup
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    obtain ⟨e, _⟩ := hn
    apply subgroup_not_le_second_cyclicTail hS i ha
    intro T x hx
    rw [← hj.2] at hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y ≫ q.hom.hom = 1 := by
      apply (e T).injective
      apply Multiplicative.toAdd.injective
      funext z
      exact Fin.elim0 z
    have hyker := (mem_range_kernelι_iff q y).mpr hy
    rw [hq.2.2.2] at hyker
    exact hyker
  obtain ⟨v, hv⟩ := hn.exists_rationalPoint_ne_one hnpos
  have hreal := semigroupRealization k G inferInstance inferInstance S hS b (cyclicTail a 2)
  obtain ⟨K, l, hl, hlc, hKs, _⟩ := hreal.1
  have hle : weightFiltration b a 2 ≤ subgroup i a := by
    rw [← hfirst]
    exact weightFiltration_antitone b a (by decide : 1 ≤ 2)
  let f := hl.homOfLe hj hle
  have hfc : IsClosedSubgroup f := hl.homOfLe_isClosedSubgroup hj hle hlc hjc
  have hf : ((weightFiltration b a 2).comap j).IsRepresentedBy f := by
    have : IsClosedImmersion f.hom.hom.left := hfc
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    ext T x
    change (∃ y, y ≫ f.hom.hom = x) ↔
      x ≫ j.hom.hom ∈ (weightFiltration b a 2).carrier T
    rw [weightFiltration, ← hl.2]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hl.homOfLe_comp_apply hj hle y).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, (cancel_mono j.hom.hom).mp ?_⟩
      rw [hl.homOfLe_comp_apply hj hle y]
      exact hy
  have hzero : (0 : characterLattice S) ∉ cyclicTail a 2 := by
    rintro ⟨m, _, hm, he⟩
    exact hS.nsmul_ne_zero ha.1 hm.ne' he
  have hKsplit : IsSplitUnipotent K := (hreal.2.2.2.1 K l hl hzero).2
  have : Smooth K.X.hom := hKs
  have : IsClosedImmersion l.hom.hom.left := hlc
  have : IsAffineHom K.X.hom := by
    rw [← l.hom.hom.w]
    infer_instance
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : IsAffineHom V.X.hom := hn.isAffineHom_overRing
  have hqc : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := hqc
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
  have : Mono f.hom.hom := hf.1
  have : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left := by
    change IsAffine (Spec (CommRingCat.of k))
    infer_instance
  obtain ⟨y, hy⟩ :=
    HomogeneousQuotient.affine_lifts_of_split_unipotent_torsors H K f q.hom.hom
      (hq.fibers_iff hf) splitUnipotentAffineTorsorStatement hKsplit
      (Over.mk (𝟙 _)) v
  refine ⟨y ≫ j.hom.hom, ?_, ?_⟩
  · rw [← hj.2]
    exact ⟨y, rfl⟩
  · intro htail
    have hyker : y ∈ ((weightFiltration b a 2).comap j).carrier _ := htail
    rw [← hq.2.2.2] at hyker
    have hyone := (mem_range_kernelι_iff q y).mp hyker
    exact hv (hy.symm.trans hyone)

/-- The root group for any higher positive multiple lies in the second
cyclic weight tail. -/
theorem subgroup_nsmul_le_second_cyclicTail
    {a : characterLattice S} (ha : a ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    subgroup i (n • a) ≤ weightFiltration (AutomorphicAction.conjugation i) a 2 := by
  rw [← cyclicRootFunctorComparison k G inferInstance inferInstance S hS i
    (n • a) (hS.nsmul_ne_zero ha (by omega))]
  apply semigroupSubgroup_mono
  rintro χ ⟨m, _, hm, he⟩
  refine ⟨m * n, ?_, Nat.mul_pos (by omega) (by omega), ?_⟩
  · have hmn : n ≤ m * n := by
      calc
        n = 1 * n := (one_mul n).symm
        _ ≤ m * n := Nat.mul_le_mul_right n hm
    omega
  · simpa only [smul_smul] using he

/-- Over every field, an actual root group has a rational point outside each
higher positive-multiple root group. -/
theorem exists_rootPoint_not_mem_nsmul_of_field
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (subgroup i (n • a)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨x, hx, hout⟩ := exists_rootPoint_not_mem_second_cyclicTail hS i ha
  exact ⟨x, hx, fun h => hout (subgroup_nsmul_le_second_cyclicTail hS i ha.1 hn _ h)⟩

/-- Choose a rational root point outside a higher-multiple root group over the
original field. -/
def rationalRootPointOutsideMultiple
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 2 ≤ n) :
    {x : rationalPoints G //
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (subgroup i (n • a)).carrier (Over.mk (𝟙 _))} :=
  ⟨Classical.choose (exists_rootPoint_not_mem_nsmul_of_field hS i ha hn),
    Classical.choose_spec (exists_rootPoint_not_mem_nsmul_of_field hS i ha hn)⟩

end Langlands.GroupScheme.RelativeRoot
