import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossCoverAction

/-! # The kernel pair of the affine tuple threshold cover -/

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
local notation "i" => E.tupleTailToTailObjectMap N p q hpq
local notation "c" => E.tupleTailCrossCoverSource N p q hpq
local notation "r" => E.tupleTailCrossCoverArrow N p q hpq
local notation "v" => E.tupleTailCrossCoverTarget N p q hpq
local notation "A" => E.tupleTailCrossCoverAction N p q hpq
local notation "e" => E.tupleTailToTailChartIso N p q hpq

@[reassoc (attr := simp)]
theorem tupleTailToTailChartIso_inv_t :
    (e).inv ≫ (H).t = Chart.t L i := by
  rw [← E.tupleTailToTailChartIso_hom_t N p q hpq, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem tupleTailToTailChartIso_inv_s :
    (e).inv ≫ (H).s = Chart.s L i := by
  rw [← E.tupleTailToTailChartIso_hom_s N p q hpq, Iso.inv_hom_id_assoc]

/-- Two cross arrows with equal lower targets determine an arrow from the
second chosen higher source to the first. -/
def tupleTailCrossCoverComparisonArrow {T : Scheme.{u}} (a b : T ⟶ P)
    (hab : a ≫ v = b ≫ v) : T ⟶ (H).R := by
  let h : (a ≫ r ≫ (L).inverse) ≫ (L).s = (b ≫ r) ≫ (L).t := by
    simpa only [Category.assoc, (L).inverse_s, tupleTailCrossCoverTarget] using hab
  let z := (L).compose (a ≫ r ≫ (L).inverse) (b ≫ r) h
  have ht : z ≫ (L).t = (a ≫ c) ≫ i := by
    dsimp only [z]
    rw [(L).compose_t, Category.assoc, Category.assoc, (L).inverse_t,
      E.tupleTailCrossCoverArrow_s, ← Category.assoc]
  have hs : z ≫ (L).s = (b ≫ c) ≫ i := by
    dsimp only [z]
    rw [(L).compose_s, Category.assoc, E.tupleTailCrossCoverArrow_s,
      ← Category.assoc]
  exact Chart.lift L i (a ≫ c) (b ≫ c) z ht hs ≫ (e).inv

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverComparisonArrow_t {T : Scheme.{u}} (a b : T ⟶ P)
    (hab : a ≫ v = b ≫ v) :
    E.tupleTailCrossCoverComparisonArrow N p q hpq a b hab ≫ (H).t = a ≫ c := by
  dsimp only [tupleTailCrossCoverComparisonArrow]
  rw [Category.assoc, E.tupleTailToTailChartIso_inv_t, Chart.lift_t]

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverComparisonArrow_s {T : Scheme.{u}} (a b : T ⟶ P)
    (hab : a ≫ v = b ≫ v) :
    E.tupleTailCrossCoverComparisonArrow N p q hpq a b hab ≫ (H).s = b ≫ c := by
  dsimp only [tupleTailCrossCoverComparisonArrow]
  rw [Category.assoc, E.tupleTailToTailChartIso_inv_s, Chart.lift_s]

/-- The action relation is the actual kernel pair of the lower target. -/
theorem tupleTailCrossCoverAction_target_isPullback :
    IsPullback (A).map (pullback.snd (H).s c) v v := by
  refine IsPullback.mk' (E.tupleTailCrossCoverAction_target N p q hpq) ?_ ?_
  · intro T a b ht hs
    exact (A).relation.hom_ext ht hs
  · intro T a b hab
    let z := E.tupleTailCrossCoverComparisonArrow N p q hpq a b hab
    have hz : z ≫ (H).s = b ≫ c :=
      E.tupleTailCrossCoverComparisonArrow_s N p q hpq a b hab
    refine ⟨pullback.lift z b hz, ?_, pullback.lift_snd _ _ _⟩
    apply E.tupleTailCrossCover_hom_ext N p q hpq
    · rw [Category.assoc, E.tupleTailCrossCoverAction_target,
        pullback.lift_snd_assoc, hab]
    · rw [Category.assoc, (A).over, pullback.lift_fst_assoc]
      exact E.tupleTailCrossCoverComparisonArrow_t N p q hpq a b hab

variable (hq : q < N + 1)

local notation "w" => E.tupleTailThresholdCover N p q hpq hq

/-- Factoring the target through the threshold open preserves the kernel pair. -/
theorem tupleTailCrossCoverAction_threshold_isPullback :
    IsPullback (A).map (pullback.snd (H).s c) w w := by
  refine IsPullback.mk'
    (E.tupleTailCrossCoverAction_threshold N p q hpq hq) ?_ ?_
  · intro T a b ht hs
    exact (A).relation.hom_ext ht hs
  · intro T a b hab
    apply (E.tupleTailCrossCoverAction_target_isPullback N p q hpq).exists_lift a b
    simpa only [Category.assoc, E.tupleTailThresholdCover_ι] using
      congrArg (· ≫
        (E.tupleChartThresholdOpen
          (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q).ι) hab

/-- The action relation arrows are isomorphic to the scheme kernel pair of the
surjective etale threshold cover. -/
def tupleTailCrossCoverKernelPairIso : (A).relation.R ≅ pullback w w :=
  (E.tupleTailCrossCoverAction_threshold_isPullback N p q hpq hq).isoPullback

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverKernelPairIso_hom_fst :
    (E.tupleTailCrossCoverKernelPairIso N p q hpq hq).hom ≫
      pullback.fst w w = (A).relation.t :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverKernelPairIso_hom_snd :
    (E.tupleTailCrossCoverKernelPairIso N p q hpq hq).hom ≫
      pullback.snd w w = (A).relation.s :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverKernelPairIso_inv_t :
    (E.tupleTailCrossCoverKernelPairIso N p q hpq hq).inv ≫
      (A).relation.t = pullback.fst w w :=
  IsPullback.isoPullback_inv_fst _

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverKernelPairIso_inv_s :
    (E.tupleTailCrossCoverKernelPairIso N p q hpq hq).inv ≫
      (A).relation.s = pullback.snd w w :=
  IsPullback.isoPullback_inv_snd _

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
