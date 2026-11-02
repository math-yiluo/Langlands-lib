import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossCoverPairKernelPair
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotient

/-! # Concrete scheme quotients on a tuple threshold -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
  (N p q : ℕ) (hpq : p ≤ q) (hq : q < N + 1)

local notation "L" => E.tupleTailPresentation N p
local notation "H" => E.tupleTailPresentation N q
local notation "c" => E.tupleTailCrossCoverSource N p q hpq
local notation "v" => E.tupleTailCrossCoverTarget N p q hpq
local notation "A" => E.tupleTailCrossCoverAction N p q hpq
local notation "B" => E.tupleTailCrossCoverPairScheme N p q hpq
local notation "a" => pullback.fst c c
local notation "b" => pullback.snd c c
local notation "k" => a ≫ c
local notation "d" => E.tupleTailCrossCoverPairArrow N p q hpq
local notation "W" => E.tupleChartThresholdOpen
  (fun j : {j : Fin (N + 1) // p ≤ j.val} => Fin.val (Subtype.val j)) q
local notation "w" => E.tupleTailThresholdCover N p q hpq hq

/-- The threshold itself is the quotient of the cross-cover action. -/
def tupleTailThresholdSchemeQuotient : (A).relation.SchemeQuotient where
  M := (W).toScheme
  q := w
  isPullback := E.tupleTailCrossCoverAction_threshold_isPullback N p q hpq hq
  etale := E.tupleTailThresholdCover_etale N p q hpq hq
  surjective := E.tupleTailThresholdCover_surjective N p q hpq hq

/-- The reversed pair arrow with both endpoints lifted to the threshold. -/
def tupleTailThresholdPairCover : B ⟶ Chart.arrows L (W).ι :=
  Chart.lift L (W).ι (b ≫ w) (a ≫ w) (d ≫ (L).inverse)
    (by rw [Category.assoc, (L).inverse_t,
      E.tupleTailCrossCoverPairArrow_s, Category.assoc,
      E.tupleTailThresholdCover_ι])
    (by rw [Category.assoc, (L).inverse_s,
      E.tupleTailCrossCoverPairArrow_t, Category.assoc,
      E.tupleTailThresholdCover_ι])

local notation "d₂" => E.tupleTailThresholdPairCover N p q hpq hq

@[reassoc (attr := simp)]
theorem tupleTailThresholdPairCover_t :
    d₂ ≫ Chart.t L (W).ι = b ≫ w :=
  Chart.lift_t _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleTailThresholdPairCover_s :
    d₂ ≫ Chart.s L (W).ι = a ≫ w :=
  Chart.lift_s _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem tupleTailThresholdPairCover_map :
    d₂ ≫ Chart.map L (W).ι = d ≫ (L).inverse :=
  Chart.lift_map _ _ _ _ _ _ _

/-- Equality after the threshold pair cover implies equality of the original
pair arrows. -/
theorem tupleTailThresholdPairCover_eq_arrow {T : Scheme.{u}} {x y : T ⟶ B}
    (h : x ≫ d₂ = y ≫ d₂) : x ≫ d = y ≫ d := by
  have h' := congrArg (· ≫ Chart.map L (W).ι ≫ (L).inverse) h
  simpa only [Category.assoc, E.tupleTailThresholdPairCover_map_assoc,
    (L).inverse_inverse, Category.comp_id] using h'

/-- The threshold relation cover is the base change of the threshold cover
along the target of its chart relation. -/
theorem tupleTailThresholdPairCover_isPullback :
    IsPullback d₂ b (Chart.t L (W).ι) w := by
  refine IsPullback.mk' (E.tupleTailThresholdPairCover_t N p q hpq hq) ?_ ?_
  · intro T x y hd hb
    exact E.tupleTailCrossCoverPair_hom_ext N p q hpq
      (E.tupleTailThresholdPairCover_eq_arrow N p q hpq hq hd) hb
  · intro T f z hfz
    have h : (f ≫ Chart.map L (W).ι ≫ (L).inverse) ≫ (L).s = z ≫ v := by
      rw [Category.assoc, Category.assoc, (L).inverse_s, Chart.map_t,
        ← Category.assoc, hfz, Category.assoc, E.tupleTailThresholdCover_ι]
    obtain ⟨x, hxd, hxb⟩ :=
      (E.tupleTailCrossCoverPairArrow_isPullback N p q hpq).exists_lift
        (f ≫ Chart.map L (W).ι ≫ (L).inverse) z h
    have hxmap : (x ≫ d₂) ≫ Chart.map L (W).ι = f ≫ Chart.map L (W).ι := by
      rw [Category.assoc, E.tupleTailThresholdPairCover_map, ← Category.assoc,
        hxd, Category.assoc, Category.assoc, (L).inverse_inverse, Category.comp_id]
    refine ⟨x, ?_, hxb⟩
    apply Chart.hom_ext L (W).ι
    · rw [Category.assoc, E.tupleTailThresholdPairCover_t, ← Category.assoc,
        hxb, hfz]
    · apply (cancel_mono (W).ι).mp
      simpa only [Category.assoc, Chart.map_s] using
        congrArg (· ≫ (L).s) hxmap

instance tupleTailThresholdPairCover_etale : Etale d₂ :=
  MorphismProperty.of_isPullback
    (E.tupleTailThresholdPairCover_isPullback N p q hpq hq).flip
    (E.tupleTailThresholdCover_etale N p q hpq hq)

instance tupleTailThresholdPairCover_surjective : Surjective d₂ :=
  MorphismProperty.of_isPullback
    (E.tupleTailThresholdPairCover_isPullback N p q hpq hq).flip
    (E.tupleTailThresholdCover_surjective N p q hpq hq)

variable (A₂ : Action (E.tupleTailPresentation N q)
  (pullback.fst (E.tupleTailCrossCoverSource N p q hpq)
    (E.tupleTailCrossCoverSource N p q hpq) ≫ E.tupleTailCrossCoverSource N p q hpq))

/-- A compatible pair action preserves the lifted threshold arrow. -/
@[reassoc]
theorem tupleTailThresholdPairAction_cover
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v) :
    A₂.map ≫ d₂ = pullback.snd (H).s k ≫ d₂ := by
  apply Chart.hom_ext L (W).ι
  · apply (cancel_mono (W).ι).mp
    simpa only [Category.assoc, E.tupleTailThresholdPairCover_t_assoc,
      E.tupleTailThresholdCover_ι] using hb
  · apply (cancel_mono (W).ι).mp
    simpa only [Category.assoc, E.tupleTailThresholdPairCover_s_assoc,
      E.tupleTailThresholdCover_ι] using ha

/-- The compatible pair action is the kernel pair of the threshold relation
cover. -/
theorem tupleTailThresholdPairAction_isPullback
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v) :
    IsPullback A₂.map (pullback.snd (H).s k) d₂ d₂ := by
  refine IsPullback.mk'
    (E.tupleTailThresholdPairAction_cover N p q hpq hq A₂ ha hb) ?_ ?_
  · intro T x y ht hs
    exact A₂.relation.hom_ext ht hs
  · intro T x y hxy
    exact (E.tupleTailCrossCoverPairAction_isPullback N p q hpq A₂ ha hb).exists_lift
      x y (E.tupleTailThresholdPairCover_eq_arrow N p q hpq hq hxy)

/-- The actual threshold arrow scheme is the quotient of a compatible pair
action. -/
def tupleTailThresholdPairSchemeQuotient
    (ha : A₂.map ≫ a ≫ v = pullback.snd (H).s k ≫ a ≫ v)
    (hb : A₂.map ≫ b ≫ v = pullback.snd (H).s k ≫ b ≫ v) :
    A₂.relation.SchemeQuotient where
  M := Chart.arrows L (W).ι
  q := d₂
  isPullback := E.tupleTailThresholdPairAction_isPullback N p q hpq hq A₂ ha hb
  etale := E.tupleTailThresholdPairCover_etale N p q hpq hq
  surjective := E.tupleTailThresholdPairCover_surjective N p q hpq hq

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
