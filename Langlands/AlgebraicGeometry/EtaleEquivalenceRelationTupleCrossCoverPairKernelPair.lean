import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossCoverPair

/-! # Kernel pairs for diagonal actions on the tuple cross-cover pair scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
  (N p q : ℕ) (hpq : p ≤ q)

local notation "L" => E.tupleTailPresentation N p
local notation "H" => E.tupleTailPresentation N q
local notation "P" => E.tupleTailCrossCoverScheme N p q hpq
local notation "c" => E.tupleTailCrossCoverSource N p q hpq
local notation "v" => E.tupleTailCrossCoverTarget N p q hpq
local notation "B" => E.tupleTailCrossCoverPairScheme N p q hpq
local notation "a" => pullback.fst c c
local notation "b" => pullback.snd c c
local notation "k" => a ≫ c
local notation "d" => E.tupleTailCrossCoverPairArrow N p q hpq

variable (A₂ : Action (E.tupleTailPresentation N q)
  (pullback.fst (E.tupleTailCrossCoverSource N p q hpq)
    (E.tupleTailCrossCoverSource N p q hpq) ≫ E.tupleTailCrossCoverSource N p q hpq))

/-- A diagonal action preserving both lower targets preserves the pair arrow. -/
@[reassoc]
theorem tupleTailCrossCoverPairAction_arrow
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v) :
    A₂.map ≫ d = pullback.snd (H).s k ≫ d := by
  apply (L).hom_ext
  · simpa only [Category.assoc, E.tupleTailCrossCoverPairArrow_t] using ha
  · simpa only [Category.assoc, E.tupleTailCrossCoverPairArrow_s] using hb

/-- The pair action has the actual pair-arrow map as its kernel-pair quotient. -/
theorem tupleTailCrossCoverPairAction_isPullback
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v) :
    IsPullback A₂.map (pullback.snd (H).s k) d d := by
  refine IsPullback.mk'
    (E.tupleTailCrossCoverPairAction_arrow N p q hpq A₂ ha hb) ?_ ?_
  · intro T x y ht hs
    exact A₂.relation.hom_ext ht hs
  · intro T x y hxy
    have hxyv : (x ≫ b) ≫ v = (y ≫ b) ≫ v := by
      simpa only [Category.assoc, E.tupleTailCrossCoverPairArrow_s] using
        congrArg (· ≫ (L).s) hxy
    let z := E.tupleTailCrossCoverComparisonArrow N p q hpq (x ≫ b) (y ≫ b) hxyv
    have hz : z ≫ (H).s = y ≫ k := by
      rw [E.tupleTailCrossCoverComparisonArrow_s]
      simpa only [Category.assoc] using
        congrArg (y ≫ ·) (pullback.condition (f := c) (g := c)).symm
    let l := pullback.lift z y hz
    have hlb : l ≫ A₂.map ≫ b = x ≫ b := by
      apply E.tupleTailCrossCover_hom_ext N p q hpq
      · rw [Category.assoc, Category.assoc, hb,
          pullback.lift_snd_assoc]
        exact hxyv.symm
      · calc
          (l ≫ A₂.map ≫ b) ≫ c = l ≫ A₂.map ≫ k := by
            simp only [Category.assoc, pullback.condition]
          _ = z ≫ (H).t := by
            rw [A₂.over, pullback.lift_fst_assoc]
          _ = (x ≫ b) ≫ c :=
            E.tupleTailCrossCoverComparisonArrow_t N p q hpq
              (x ≫ b) (y ≫ b) hxyv
    refine ⟨l, ?_, pullback.lift_snd _ _ _⟩
    apply E.tupleTailCrossCoverPair_hom_ext N p q hpq
    · rw [Category.assoc,
        E.tupleTailCrossCoverPairAction_arrow N p q hpq A₂ ha hb,
        pullback.lift_snd_assoc]
      exact hxy.symm
    · exact hlb

/-- A finite invariant affine quotient cover for a compatible pair action. -/
def tupleTailCrossCoverPairActionAffineQuotientCover
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v)
    (hq : q < N + 1) :
    A₂.relation.InvariantAffineQuotientCover := by
  let : IsAffine A₂.relation.U :=
    E.tupleTailCrossCoverPairScheme_isAffine N p q hpq
  exact @invariantAffineQuotientCoverOfCompactImage A₂.relation (L).R d
    (E.tupleTailCrossCoverPairAction_isPullback N p q hpq A₂ ha hb)
    inferInstance inferInstance (E.tupleTailCrossCoverPairArrow_etale N p q hpq)
    (E.tupleTailCrossCoverPairImageOpen N p q)
    (E.tupleTailCrossCoverPairImageOpen_isCompact N p q)
    (E.tupleTailCrossCoverPairArrow_range N p q hpq hq)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
