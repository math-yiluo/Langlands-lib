import Langlands.GroupScheme.RelativeLevi.SplitBorelUnipotentCommutator
import Langlands.GroupScheme.Reductive.LocalSplitWeightSubgroup
import Langlands.GroupScheme.RelativeUnipotent.RootWeightFiltration

/-! # Independent nonnegative weights inside a regular contracting group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

open Langlands.GroupTheory

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G U : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  (j : U ⟶ G) (hu : TorusEquivariant i ch u) (ν : I → ℤ)
  (hU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i ν)).IsRepresentedBy j)
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
  (hpos : ∀ p, 0 < coPairing (ch (pos p)) ν)

variable [IsOpenImmersion (cellMap i u neg pos).left]
  (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)

include hneg

/-- Standard commutators in the regular contracting group satisfy the sum
bound for an independent cocharacter, allowing zero input weights. -/
theorem exists_unipotent_commutator_eq_weight_ge_of_regular
    (wt : I → ℤ) (k l : Fin n)
    (hk : 0 ≤ coPairing (ch (pos k)) wt)
    (hl : 0 ≤ coPairing (ch (pos l)) wt) (Z : Over (Spec (CommRingCat.of R)))
    (x y : Γ(Z.left, ⊤)) :
    ∃ c : Fin n → Γ(Z.left, ⊤),
      ⁅rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z x,
        rootPoint (positiveRootToUnipotent j hu ν hU hpos l) Z y⁆ =
        (List.ofFn fun p =>
          rootPoint (positiveRootToUnipotent j hu ν hU hpos p) Z (c p)).prod ∧
      ∀ p, coPairing (ch (pos p)) wt <
        coPairing (ch (pos k)) wt + coPairing (ch (pos l)) wt → c p = 0 := by
  obtain ⟨c, hc, hlow⟩ := exists_posComm_eq_weight_ge_of_regular
    (neg := neg) hu ν hneg hpos wt l k hl hk Z (-y) (-x)
  refine ⟨c, ?_, fun p hp => hlow p (by simpa [add_comm] using hp)⟩
  have hstandard :
      ⁅rootPoint (u (pos k)) Z x, rootPoint (u (pos l)) Z y⁆ =
        orderedProduct u pos Z c := by
    rw [← hc, posComm, rootPoint_neg, rootPoint_neg, commutatorElement_def]
    group
  let := hU.1
  apply (cancel_mono j.hom.hom).mp
  rw [orderedProduct_positiveRootToUnipotent_comp]
  simpa only [commutatorElement_def, MonObj.mul_comp, GrpObj.inv_comp,
    positiveRootToUnipotent, rootPoint_rootToUnipotent_comp] using hstandard

/-- The actual positive root factors satisfy the sum bound for an independent
natural weight family; no strict positivity of these weights is required. -/
theorem commutator_unipotent_rootFactor_le_of_regular
    (wt : I → ℤ) (w : Fin n → ℕ)
    (hw : ∀ p, coPairing (ch (pos p)) wt = (w p : ℤ))
    (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n) :
    ⁅rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z k,
      rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z l⁆ ≤
      HeightFiltration.level
        (rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z)
        w (w k + w l) := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨c, hc, hlow⟩ := exists_unipotent_commutator_eq_weight_ge_of_regular
    j hu ν hU hpos hneg wt k l
      (by rw [hw k]; exact_mod_cast Nat.zero_le (w k))
      (by rw [hw l]; exact_mod_cast Nat.zero_le (w l)) Z x.toAdd y.toAdd
  change ⁅rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z x.toAdd,
    rootPoint (positiveRootToUnipotent j hu ν hU hpos l) Z y.toAdd⁆ ∈ _
  rw [hc]
  apply (HeightFiltration.level
    (rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z)
    w (w k + w l)).list_prod_mem
  intro a ha
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
  by_cases hp : w k + w l ≤ w p
  · exact HeightFiltration.le_level _ _ hp
      (mem_rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z p (c p))
  · have hc0 : c p = 0 := hlow p (by rw [hw p, hw k, hw l]; omega)
    rw [hc0, rootPoint_zero]
    exact one_mem _

variable [IsAffine U.X.left]

/-- The specified regular cell, with its actual factored roots, defines a
root-height chart. No opaque chart choice or root reordering is used. -/
def positiveCellRootHeightChart : RelativeUnipotent.RootHeightChart U where
  dimension := n
  roots := liftedPositiveRootToUnipotent j hu ν hU hpos
  height := fun p => (coPairing (ch (pos p)) ν).toNat
  height_pos := fun p => by
    have hk := hpos p
    have he := Int.toNat_of_nonneg hk.le
    omega
  chart := positiveProductIso j hu ν hU hneg hpos
  formula := fun _ x => comp_positiveProductIso_hom j hu ν hU hneg hpos x
  commutator := commutator_unipotent_rootFactor_le j hu ν hU hpos hneg _
    (fun p => (Int.toNat_of_nonneg (hpos p).le).symm)

/-- An independent cocharacter nonnegative on the positive list gives actual
weight data on the specified regular-cell chart, including zero weights. -/
def positiveCellRootWeightData (wt : I → ℤ)
    (hwt : ∀ p, 0 ≤ coPairing (ch (pos p)) wt) :
    RelativeUnipotent.RootWeightData
      (positiveCellRootHeightChart j hu ν hU hpos hneg) where
  weight := fun p => (coPairing (ch (pos p)) wt).toNat
  commutator := commutator_unipotent_rootFactor_le_of_regular
    j hu ν hU hpos hneg wt _
      (fun p => (Int.toNat_of_nonneg (hwt p)).symm)

end Langlands.GroupScheme.LocalSplitCell
