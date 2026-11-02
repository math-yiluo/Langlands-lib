import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationSaturation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAction

/-! # The higher-tail action on a tuple cross cover -/

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

/-- The higher-tail map on relation arrows. -/
abbrev tupleTailToTailRelationMap : (H).R ⟶ (L).R :=
  E.tupleChartReindexRelationMap
    (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val)
    (tupleTailIndexMap N p q hpq)

local notation "g" => E.tupleTailToTailRelationMap N p q hpq

@[reassoc (attr := simp)]
theorem tupleTailToTailRelationMap_t : g ≫ (L).t = (H).t ≫ i :=
  E.tupleChartReindexRelationMap_t _ _

@[reassoc (attr := simp)]
theorem tupleTailToTailRelationMap_s : g ≫ (L).s = (H).s ≫ i :=
  E.tupleChartReindexRelationMap_s _ _

@[reassoc (attr := simp)]
theorem tupleTailToTailChartIso_hom_t :
    (E.tupleTailToTailChartIso N p q hpq).hom ≫ Chart.t L i = (H).t := by
  simp only [tupleTailToTailChartIso, E.tupleChartReindexChartIso_hom,
    E.tupleChartReindexChartMap_t]

@[reassoc (attr := simp)]
theorem tupleTailToTailChartIso_hom_s :
    (E.tupleTailToTailChartIso N p q hpq).hom ≫ Chart.s L i = (H).s := by
  simp only [tupleTailToTailChartIso, E.tupleChartReindexChartIso_hom,
    E.tupleChartReindexChartMap_s]

/-- A cross-cover map is determined by its lower target and higher source. -/
theorem tupleTailCrossCover_hom_ext {T : Scheme.{u}} {a b : T ⟶ P}
    (ht : a ≫ v = b ≫ v) (hs : a ≫ c = b ≫ c) : a = b := by
  apply pullback.hom_ext
  · apply (L).hom_ext
    · exact ht
    · change (a ≫ r) ≫ (L).s = (b ≫ r) ≫ (L).s
      rw [Category.assoc, Category.assoc, E.tupleTailCrossCoverArrow_s,
        ← Category.assoc, hs, Category.assoc]
  · exact hs

/-- Acting changes the chosen source by the higher-tail arrow and preserves
the lower-tail target. -/
def tupleTailCrossCoverActionMap : pullback (H).s c ⟶ P := by
  let a := pullback.fst (H).s c
  let b := pullback.snd (H).s c
  have hab : (b ≫ r) ≫ (L).s = (a ≫ g ≫ (L).inverse) ≫ (L).t := by
    dsimp only [a, b]
    rw [Category.assoc, E.tupleTailCrossCoverArrow_s,
      Category.assoc, Category.assoc, (L).inverse_t, E.tupleTailToTailRelationMap_s]
    exact (pullback.condition_assoc i).symm
  refine pullback.lift ((L).compose (b ≫ r) (a ≫ g ≫ (L).inverse) hab)
    (a ≫ (H).t) ?_
  rw [(L).compose_s, Category.assoc, Category.assoc, (L).inverse_s,
    E.tupleTailToTailRelationMap_t, ← Category.assoc]

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverActionMap_source :
    E.tupleTailCrossCoverActionMap N p q hpq ≫ c =
      pullback.fst (H).s c ≫ (H).t :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverActionMap_target :
    E.tupleTailCrossCoverActionMap N p q hpq ≫ v =
      pullback.snd (H).s c ≫ v := by
  dsimp only [tupleTailCrossCoverActionMap, tupleTailCrossCoverTarget]
  rw [← Category.assoc, pullback.lift_fst, (L).compose_t, Category.assoc]

/-- The actual higher-tail action on the affine cross cover. -/
def tupleTailCrossCoverAction : Action H c := by
  refine ⟨E.tupleTailCrossCoverActionMap N p q hpq,
    E.tupleTailCrossCoverActionMap_source N p q hpq, ?_, ?_⟩
  ·
    apply E.tupleTailCrossCover_hom_ext N p q hpq
    · simp only [Category.assoc, E.tupleTailCrossCoverActionMap_target,
        pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc, E.tupleTailCrossCoverActionMap_source,
        pullback.lift_fst_assoc, (H).unit_t, Category.comp_id, Category.id_comp]
  ·
    intro T a b x hab hbx
    apply E.tupleTailCrossCover_hom_ext N p q hpq
    · simp only [Category.assoc, E.tupleTailCrossCoverActionMap_target,
        pullback.lift_snd_assoc]
    · simp only [Category.assoc, E.tupleTailCrossCoverActionMap_source,
        pullback.lift_fst_assoc, (H).compose_t]

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverAction_target :
    (E.tupleTailCrossCoverAction N p q hpq).map ≫ v =
      pullback.snd (H).s c ≫ v :=
  E.tupleTailCrossCoverActionMap_target N p q hpq

/-- The threshold cover is invariant under the higher-tail action. -/
@[reassoc]
theorem tupleTailCrossCoverAction_threshold (hq : q < N + 1) :
    (E.tupleTailCrossCoverAction N p q hpq).map ≫
        E.tupleTailThresholdCover N p q hpq hq =
      pullback.snd (H).s c ≫ E.tupleTailThresholdCover N p q hpq hq := by
  apply (cancel_mono
    (E.tupleChartThresholdOpen
      (fun j : {j : Fin (N + 1) // p ≤ j.val} => j.val.val) q).ι).mp
  simp only [Category.assoc, E.tupleTailThresholdCover_ι,
    E.tupleTailCrossCoverAction_target]

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
