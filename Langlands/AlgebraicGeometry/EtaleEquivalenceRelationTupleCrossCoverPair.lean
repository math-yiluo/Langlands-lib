import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossCoverQuotientCover

/-! # The pair scheme of the tuple cross cover -/

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
local notation "P" => E.tupleTailCrossCoverScheme N p q hpq
local notation "c" => E.tupleTailCrossCoverSource N p q hpq
local notation "r" => E.tupleTailCrossCoverArrow N p q hpq
local notation "v" => E.tupleTailCrossCoverTarget N p q hpq

/-- Pairs of lower-tail arrows with the same chosen higher-tail source. -/
abbrev tupleTailCrossCoverPairScheme : Scheme.{u} := pullback c c

local notation "B" => E.tupleTailCrossCoverPairScheme N p q hpq
local notation "a" => pullback.fst c c
local notation "b" => pullback.snd c c

/-- The lower-tail arrow obtained by composing the first cross arrow with the
inverse of the second. -/
def tupleTailCrossCoverPairArrow : B ⟶ (L).R :=
  (L).compose (a ≫ r) (b ≫ r ≫ (L).inverse) (by
    rw [Category.assoc, E.tupleTailCrossCoverArrow_s,
      Category.assoc, Category.assoc, (L).inverse_t,
      E.tupleTailCrossCoverArrow_s]
    exact pullback.condition_assoc _)

local notation "d" => E.tupleTailCrossCoverPairArrow N p q hpq

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverPairArrow_t :
    d ≫ (L).t = a ≫ v := by
  dsimp only [tupleTailCrossCoverPairArrow]
  rw [(L).compose_t]
  rfl

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverPairArrow_s :
    d ≫ (L).s = b ≫ v := by
  dsimp only [tupleTailCrossCoverPairArrow]
  rw [(L).compose_s, Category.assoc, Category.assoc, (L).inverse_s]
  rfl

/-- A pair is determined by its lower relation arrow and its second cross arrow. -/
theorem tupleTailCrossCoverPair_hom_ext {T : Scheme.{u}} {x y : T ⟶ B}
    (hd : x ≫ d = y ≫ d) (hb : x ≫ b = y ≫ b) : x = y := by
  apply pullback.hom_ext
  · apply E.tupleTailCrossCover_hom_ext N p q hpq
    · simpa only [Category.assoc, E.tupleTailCrossCoverPairArrow_t] using
        congrArg (· ≫ (L).t) hd
    · simpa only [Category.assoc, pullback.condition] using congrArg (· ≫ c) hb
  · exact hb

/-- The pair-to-arrow map is the base change of the cross-cover target along
the source of the lower-tail relation. -/
theorem tupleTailCrossCoverPairArrow_isPullback :
    IsPullback d b (L).s v := by
  refine IsPullback.mk' (E.tupleTailCrossCoverPairArrow_s N p q hpq) ?_ ?_
  · intro T x y hd hb
    exact E.tupleTailCrossCoverPair_hom_ext N p q hpq hd hb
  · intro T f z hfz
    have hfr : f ≫ (L).s = (z ≫ r) ≫ (L).t := by
      simpa only [Category.assoc, tupleTailCrossCoverTarget] using hfz
    let x : T ⟶ P :=
      pullback.lift ((L).compose f (z ≫ r) hfr) (z ≫ c) (by
        rw [(L).compose_s, Category.assoc, E.tupleTailCrossCoverArrow_s,
          Category.assoc])
    have hxc : x ≫ c = z ≫ c := pullback.lift_snd _ _ _
    have hxv : x ≫ v = f ≫ (L).t := by
      dsimp only [x, tupleTailCrossCoverTarget]
      rw [pullback.lift_fst_assoc, (L).compose_t]
    refine ⟨pullback.lift x z hxc, ?_, pullback.lift_snd _ _ _⟩
    apply (L).hom_ext
    · rw [Category.assoc, E.tupleTailCrossCoverPairArrow_t,
        pullback.lift_fst_assoc, hxv]
    · rw [Category.assoc, E.tupleTailCrossCoverPairArrow_s,
        pullback.lift_snd_assoc, hfz]

instance tupleTailCrossCoverPairScheme_isAffine : IsAffine B := by
  dsimp only [tupleTailCrossCoverPairScheme]
  infer_instance

instance tupleTailCrossCoverPairArrow_etale : Etale d :=
  MorphismProperty.of_isPullback
    (E.tupleTailCrossCoverPairArrow_isPullback N p q hpq).flip
    (E.tupleTailCrossCoverTarget_etale N p q hpq)

/-- The open of lower-tail arrows supported on the higher threshold. -/
def tupleTailCrossCoverPairImageOpen : (L).R.Opens :=
  (L).s ⁻¹ᵁ E.tupleChartThresholdOpen
    (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q

theorem tupleTailCrossCoverPairImageOpen_isCompact :
    IsCompact (E.tupleTailCrossCoverPairImageOpen N p q : Set (L).R) :=
  (L).s.isCompact_preimage (E.tupleChartThresholdOpen_isCompact _ q)

/-- The pair-to-arrow map covers exactly the arrows supported on the higher
threshold. -/
theorem tupleTailCrossCoverPairArrow_range (hq : q < N + 1) :
    Set.range d =
      (E.tupleTailCrossCoverPairImageOpen N p q : Set (L).R) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    change (L).s (d z) ∈ E.tupleChartThresholdOpen _ q
    change (d ≫ (L).s) z ∈ E.tupleChartThresholdOpen _ q
    rw [E.tupleTailCrossCoverPairArrow_s]
    change v (b z) ∈ (E.tupleChartThresholdOpen
      (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q : Set (L).U)
    rw [← E.tupleTailCrossCoverTarget_range N p q hpq hq]
    exact ⟨b z, rfl⟩
  · intro hx
    change (L).s x ∈ (E.tupleChartThresholdOpen
      (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q : Set (L).U) at hx
    rw [← E.tupleTailCrossCoverTarget_range N p q hpq hq] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
      (E.tupleTailCrossCoverPairArrow_isPullback N p q hpq) x z hz.symm
    exact ⟨y, hy⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
