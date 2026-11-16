import Langlands.GroupScheme.RelativeLevi.SplitBorelPositiveFactors
import Langlands.GroupScheme.Reductive.LocalSplitHeightSubgroup

/-! # Height commutator bounds inside the actual contracting group -/

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

/-- The positive root family indexed in the universe of the base ring. -/
def liftedPositiveRootToUnipotent : ULift.{u} (Fin n) → (Ga R ⟶ U) :=
  fun p => positiveRootToUnipotent j hu ν hU hpos p.down

variable [IsOpenImmersion (cellMap i u neg pos).left]
  (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)

include hneg

/-- Standard commutators in the contracting group have coordinates supported
at weights at least the sum of their input weights, on every test scheme. -/
theorem exists_unipotent_commutator_eq_weight_ge
    (k l : Fin n) (Z : Over (Spec (CommRingCat.of R)))
    (x y : Γ(Z.left, ⊤)) :
    ∃ c : Fin n → Γ(Z.left, ⊤),
      ⁅rootPoint (positiveRootToUnipotent j hu ν hU hpos k) Z x,
        rootPoint (positiveRootToUnipotent j hu ν hU hpos l) Z y⁆ =
        (List.ofFn fun p =>
          rootPoint (positiveRootToUnipotent j hu ν hU hpos p) Z (c p)).prod ∧
      ∀ p, coPairing (ch (pos p)) ν <
        coPairing (ch (pos k)) ν + coPairing (ch (pos l)) ν → c p = 0 := by
  obtain ⟨c, hc, hlow⟩ := exists_posComm_eq_weight_ge
    (neg := neg) hu ν hneg hpos l k Z (-y) (-x)
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

/-- The positive root factors inside the actual contracting group satisfy
the standard subgroup commutator bound for their natural heights. -/
theorem commutator_unipotent_rootFactor_le
    (w : Fin n → ℕ) (hw : ∀ p, coPairing (ch (pos p)) ν = (w p : ℤ))
    (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n) :
    ⁅rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z k,
      rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z l⁆ ≤
      HeightFiltration.level
        (rootFactor (liftedPositiveRootToUnipotent j hu ν hU hpos) ULift.up Z)
        w (w k + w l) := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨c, hc, hlow⟩ := exists_unipotent_commutator_eq_weight_ge
    j hu ν hU hpos hneg k l Z x.toAdd y.toAdd
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

end Langlands.GroupScheme.LocalSplitCell
