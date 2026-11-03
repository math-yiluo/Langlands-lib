import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Mathlib.Data.Nat.Prime.Defs

/-! # The full actual rank-one conclusion from opposite-pair existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Every nonidentity rational actual root point admits an opposite pair
whose product normalizes the given torus. No other conclusion is included. -/
def HasOppositeFactorPairs : Prop :=
  ∀ (a : characterLattice T), a ∈ relativeRoots i →
    ∀ (x : rationalPoints G),
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) → x ≠ 1 →
      ∃ p : rationalPoints G × rationalPoints G, IsOppositeFactorPair i a x p

/-- The integral coroot of a pair at a nonzero multiple forces the
multiplier to divide two. The base character need not itself be a root. -/
theorem IsOppositeFactorPair.eq_one_or_two_of_nsmul
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} {n : ℕ}
    (ha : n • a ≠ 0) {x : rationalPoints G}
    (hx : x ∈ (subgroup i (n • a)).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i (n • a) x p) : n = 1 ∨ n = 2 := by
  have hpair := (hp.coroot_spec i hT ha hx hx1).1
  have hz : (2 : ℤ) =
      (n : ℤ) * latticePairing T a (hp.coroot i hT ha hx hx1) := by
    simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using hpair.symm
  have hd : (n : ℤ) ∣ (2 : ℤ) := ⟨_, hz⟩
  exact (Nat.dvd_prime Nat.prime_two).mp (Int.natCast_dvd_natCast.mp hd)

/-- Rational nontriviality and opposite-pair existence bound every
actual root multiple, without a relative-root-system hypothesis. -/
theorem HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    {a : characterLattice T} {n : ℕ} (hn : n • a ∈ relativeRoots i) :
    n = 1 ∨ n = 2 := by
  obtain ⟨x, hx, hx1⟩ := exists_rootPoint_actual hT i hn
  obtain ⟨p, hp⟩ := hE (n • a) hn x hx hx1
  exact hp.eq_one_or_two_of_nsmul i hT hn.1 hx hx1

/-- Under pair existence, absence of the double excludes every higher
positive multiple, even without membership of the base character. -/
theorem HasOppositeFactorPairs.hasNoHigherRoots_of_two_not_mem [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    {a : characterLattice T} (h2 : (2 : ℤ) • a ∉ relativeRoots i) :
    HasNoHigherRoots i a := by
  intro n hn hroot
  rcases hE.eq_one_or_two_of_nsmul_mem i hT hroot with h | h
  · omega
  · subst n
    exact h2 (by simpa only [two_zsmul, two_nsmul] using hroot)

/-- An actual pair's root flip transports absence of higher roots
to the opposite ray. No separate root-negation theorem is used. -/
theorem IsOppositeFactorPair.hasNoHigherRoots_neg
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {x : rationalPoints G}
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) (hpos : HasNoHigherRoots i a) :
    HasNoHigherRoots i (-a) := by
  intro n hn hroot
  have h := weylAction_mapsTo_relativeRoots i
    (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) hroot
  rw [map_nsmul, map_neg, hp.weylAction_eq_neg i hT ha hx hx1, neg_neg] at h
  exact hpos n hn h

/-- For a smooth affine group with a split subtorus, pair existence is
the sole remaining premise for the full existing rank-one predicate. -/
theorem hasRankOneFactorization_of_hasOppositeFactorPairs [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i) :
    HasRankOneFactorization i := by
  intro a ha x hx hx1
  obtain ⟨p, hp⟩ := hE a ha x hx hx1
  refine ⟨⟨p, hp, ?_⟩, ?_⟩
  · intro q hq
    exact hq.eq i hT ha.1 hx hx1 hp
  · intro q hq
    obtain ⟨hq1, hq2⟩ := hq.factors_ne_one i hT ha.1 hx hx1
    refine ⟨hq1, hq2, hq.isRelativeReflection i hT ha hx hx1, ?_⟩
    intro h2
    have hpos := hE.hasNoHigherRoots_of_two_not_mem i hT h2
    have hneg := hq.hasNoHigherRoots_neg i hT ha.1 hx hx1 hpos
    exact hq.nonmultipliable_consequences_of_noHigherRoots i
      inferInstance hT ha.1 hpos hneg hx hx1

/-- Over smooth affine groups with split subtori, the full rank-one
predicate and the existence-only predicate are equivalent. -/
theorem hasRankOneFactorization_iff_hasOppositeFactorPairs [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) :
    HasRankOneFactorization i ↔ HasOppositeFactorPairs i := by
  constructor
  · intro h a ha x hx hx1
    exact (h a ha x hx hx1).1.exists
  · exact hasRankOneFactorization_of_hasOppositeFactorPairs i hT

end Langlands.GroupScheme.RelativeRoot
