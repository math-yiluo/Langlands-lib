import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleRoots
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.SemigroupTriviality
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.GroupTheory.Commutator.Basic

/-! # Mixed simple-root semigroups and all-test commutation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

section PositiveCone

variable {I M : Type*} [Fintype I] [AddCommGroup M]
    {v : I → M} (hv : LinearIndependent ℤ v)

include hv in
/-- A positive multiple of one independent generator minus a positive multiple
of another cannot lie in their nonnegative additive monoid. -/
theorem mixed_not_mem_positiveClosure (a b : I) (hab : a ≠ b)
    (n m : ℕ) (hm : 0 < m) :
    n • v a - m • v b ∉ AddSubmonoid.closure (Set.range v) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := AddSubmonoid.exists_of_mem_closure_range v _ h
  let d : I → ℤ := Pi.single a (n : ℤ) - Pi.single b (m : ℤ)
  have hd : ∑ j, d j • v j = n • v a - m • v b := by
    simp [d, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul]
  have heq : ∑ j, (c j : ℤ) • v j = ∑ j, d j • v j := by
    rw [hd, hc]
    simp
  have hcoef := Fintype.linearIndependent_iffₛ.mp hv
    (fun j => (c j : ℤ)) d heq b
  simp [d, hab.symm] at hcoef
  omega

end PositiveCone

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G)

/-- The literal sum of positive cyclic tails for a character and the negative
of another. These are the possible weights in their commutator bound. -/
def mixedRootSemigroup (a b : characterLattice T) :
    AddSubsemigroup (characterLattice T) :=
  RelativeRoot.semigroupSum (RelativeRoot.cyclicTail a 1)
    (RelativeRoot.cyclicTail (-b) 1)

theorem mem_mixedRootSemigroup_iff (a b x : characterLattice T) :
    x ∈ mixedRootSemigroup a b ↔
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n • a - m • b = x := by
  constructor
  · rintro ⟨y, ⟨n, _, hn, rfl⟩, z, ⟨m, _, hm, rfl⟩, heq⟩
    exact ⟨n, m, hn, hm, by simpa only [smul_neg, sub_eq_add_neg] using heq⟩
  · rintro ⟨n, m, hn, hm, heq⟩
    refine ⟨n • a, ⟨n, by omega, hn, rfl⟩,
      m • (-b), ⟨m, by omega, hm, rfl⟩, ?_⟩
    simpa only [smul_neg, sub_eq_add_neg] using heq

section RealizingDatum

variable {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (ν : cocharacterLattice T)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)

include hP hν hT in
/-- Both signs of a strict mixed simple-root combination lie outside the
positive simple-root monoid. -/
theorem mixed_simple_not_mem_positive
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • (a : characterLattice T) - m • b ∉
        AddSubmonoid.closure (simpleRelativeRoots i ν) ∧
      -(n • (a : characterLattice T) - m • b) ∉
        AddSubmonoid.closure (simpleRelativeRoots i ν) := by
  classical
  let : Fintype (simpleRelativeRoots i ν) :=
    (hT.finite_simpleRelativeRoots i ν).fintype
  have hli := linearIndependent_simpleRoots i P hP ν hT hν
  constructor
  · simpa only [Subtype.range_coe] using
      mixed_not_mem_positiveClosure hli a b hab n m hm
  · have h := mixed_not_mem_positiveClosure hli b a hab.symm m n hn
    simpa only [Subtype.range_coe, neg_sub] using h

include hP hν hT in
/-- A strict mixed combination of distinct simple roots is nonzero and is
not an actual root, without a reducedness hypothesis. -/
theorem mixed_simple_ne_zero_not_root
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • (a : characterLattice T) - m • b ≠ 0 ∧
      n • (a : characterLattice T) - m • b ∉ roots i := by
  let x := n • (a : characterLattice T) - m • b
  obtain ⟨hpos, hneg⟩ := mixed_simple_not_mem_positive i P hP ν hT hν a b hab n m hn hm
  have hclosure := closure_simpleRoots_eq_positive i P hP ν hT
  refine ⟨?_, ?_⟩
  · intro hx
    apply hpos
    rw [hx]
    exact AddSubmonoid.zero_mem _
  · intro hx
    have hxν : latticePairing T x ν ≠ 0 := hν x hx
    rcases lt_or_gt_of_ne hxν with hnegative | hpositive
    · apply hneg
      rw [hclosure]
      apply AddSubmonoid.subset_closure
      refine ⟨?_, ?_⟩
      · change -x ∈ roots i
        rw [← hP.2.1]
        apply P.neg_mem_range_root_iff.mpr
        rwa [hP.2.1]
      · change 0 < latticePairing T (-x) ν
        simpa only [map_neg, LinearMap.neg_apply] using neg_pos.mpr hnegative
    · apply hpos
      rw [hclosure]
      exact AddSubmonoid.subset_closure ⟨hx, hpositive⟩

include hP hν hT in
/-- Every character in the mixed commutator semigroup is nonzero and is
absent from the ambient root set. -/
theorem mixedRootSemigroup_has_no_roots
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    {x : characterLattice T} (hx : x ∈ mixedRootSemigroup (a : characterLattice T) b) :
    x ≠ 0 ∧ x ∉ roots i := by
  obtain ⟨n, m, hn, hm, rfl⟩ := (mem_mixedRootSemigroup_iff _ _ _).mp hx
  exact mixed_simple_ne_zero_not_root i P hP ν hT hν a b hab n m hn hm

include hP hν hT in
/-- The mixed simple/opposite semigroup generates the identity subgroup on
every scheme test. -/
theorem mixedRoot_semigroupSubgroup_eq_bot
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b) :
    RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
      (mixedRootSemigroup (a : characterLattice T) b) = ⊥ := by
  apply RelativeRoot.semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization
    (AutomorphicAction.conjugation i) hT
  intro x hx hweight
  obtain ⟨hx0, hxroot⟩ := mixedRootSemigroup_has_no_roots i P hP ν hT hν a b hab hx
  exact hxroot ((RelativeRoot.mem_actionWeightSupport_conjugation_iff i hx0).mp hweight)

include hP hν hT in
/-- Distinct simple and opposite-simple intrinsic root groups commute on all
tests, including nonreduced schemes, over every field. -/
theorem commute_simple_opposite [Smooth G.X.hom]
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    {W : Over (Spec (CommRingCat.of k))} {x y : W ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup i (a : characterLattice T)).carrier W)
    (hy : y ∈ (RelativeRoot.subgroup i (-(b : characterLattice T))).carrier W) :
    Commute x y := by
  let c := AutomorphicAction.conjugation i
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup c
      (RelativeRoot.cyclicTail (a : characterLattice T) 1)).carrier W := by
    change x ∈ (RelativeRoot.weightFiltration c (a : characterLattice T) 1).carrier W
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT i _ a.2.1.1.1]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup c
      (RelativeRoot.cyclicTail (-(b : characterLattice T)) 1)).carrier W := by
    change y ∈ (RelativeRoot.weightFiltration c (-(b : characterLattice T)) 1).carrier W
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT i _ (neg_ne_zero.mpr b.2.1.1.1)]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G inferInstance inferInstance T hT c
    (RelativeRoot.cyclicTail (a : characterLattice T) 1)
    (RelativeRoot.cyclicTail (-(b : characterLattice T)) 1) W x y hx' hy'
  change x * y * x⁻¹ * y⁻¹ ∈ (RelativeRoot.semigroupSubgroup c
    (mixedRootSemigroup (a : characterLattice T) b)).carrier W at h
  rw [mixedRoot_semigroupSubgroup_eq_bot i P hP ν hT hν a b hab] at h
  have heq : x * y * x⁻¹ * y⁻¹ = 1 := h
  exact commutatorElement_eq_one_iff_commute.mp heq

end RealizingDatum

end Langlands.GroupScheme.LeviGluing
