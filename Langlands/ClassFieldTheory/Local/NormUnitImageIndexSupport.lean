import Langlands.ClassFieldTheory.Local.NormExistenceFiniteSupport
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel
import Mathlib.GroupTheory.Index

/-! # Index arithmetic for norm images of unit filtrations

Abstract subgroup-index lemmas for commutative groups, the counting argument
that turns divisibility bounds into an exact norm-quotient cardinality, and the
local norm index `[Fˣ : N(Eˣ)] = [E : F]` for fields in independent universes.
-/

noncomputable section

namespace Langlands.LocalClassField.NormUnitImage

universe u v

section Index

variable {G G' : Type*} [Group G] [CommGroup G']

/-- Adding a common subgroup `A` and applying a homomorphism can only divide
a relative index: `[A·f(B) : A·f(D)]` divides `[B : D]`. -/
theorem relIndex_sup_map_dvd (f : G →* G') (A : Subgroup G') {D B : Subgroup G}
    (hDB : D ≤ B) :
    (A ⊔ D.map f).relIndex (A ⊔ B.map f) ∣ D.relIndex B := by
  have hsup : B.map f ⊔ (A ⊔ D.map f) = A ⊔ B.map f := by
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left
        ((Subgroup.map_mono hDB).trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have hD : D ≤ (A ⊔ D.map f).comap f :=
    Subgroup.map_le_iff_le_comap.mp le_sup_right
  rw [← hsup, Subgroup.relIndex_sup_right, ← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B hD

/-- The image version with no added subgroup. -/
theorem relIndex_map_dvd (f : G →* G') {D B : Subgroup G} (hDB : D ≤ B) :
    (D.map f).relIndex (B.map f) ∣ D.relIndex B := by
  simpa using relIndex_sup_map_dvd f ⊥ hDB

/-- A subgroup's order is the order of its image times the order of its
intersection with the kernel. -/
theorem card_eq_card_map_mul_card_inf_ker {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (f : G₁ →* G₂) (S : Subgroup G₁) :
    Nat.card S = Nat.card (S.map f) * Nat.card (f.ker ⊓ S : Subgroup G₁) := by
  rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_bot_left,
    ← Subgroup.relIndex_mul_relIndex ⊥ (f.ker ⊓ S) S bot_le inf_le_right,
    Subgroup.inf_relIndex_right, mul_comm]

/-- The counting argument. Suppose `Nm` has nonzero index, `V ≤ Nm ⊓ Un`,
`[Un : V]` divides `c`, and `[G' : Un ⊔ Nm] * c` divides `[G' : Nm]`. Then the
image of `Un` in `G' / Nm` has exactly `c` elements. -/
theorem card_map_mk_eq_of_dvd {Nm Un V : Subgroup G'} {c : ℕ}
    (hidx : Nm.index ≠ 0) (hVN : V ≤ Nm) (hVU : V.relIndex Un ∣ c)
    (htop : (Un ⊔ Nm).index * c ∣ Nm.index) :
    Nat.card (Un.map (QuotientGroup.mk' Nm)) = c := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have hsplit : Nm.index = (Un ⊔ Nm).index * Nm.relIndex Un := by
    rw [← Subgroup.relIndex_sup_right Un Nm, mul_comm]
    exact (Subgroup.relIndex_mul_index le_sup_right).symm
  have hz : (Un ⊔ Nm).index ≠ 0 := by
    intro h
    rw [hsplit, h, zero_mul] at hidx
    exact hidx rfl
  have hc : c ∣ Nm.relIndex Un := by
    rw [hsplit] at htop
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hz)).mp htop
  exact Nat.dvd_antisymm ((Subgroup.relIndex_dvd_of_le_left Un hVN).trans hVU) hc

end Index

section NormIndex

variable {p : ℕ} [Fact p.Prime]

/-- The local norm index for an abelian extension whose fields lie in
independent universes, transported from the universe-zero models. -/
theorem normSubgroup_index_eq_finrank (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] :
    (normSubgroup F.Carrier E.Carrier).index = Module.finrank F.Carrier E.Carrier := by
  let := NYLL.universeZeroAlgebra F E
  have := NYLL.universeZeroAlgebra_finiteDimensional F E
  have := NYLL.universeZeroAlgebra_isAbelianGalois F E
  let e := Units.mapEquiv (NYLL.universeZeroEquiv F).toRingEquiv.toMulEquiv
  have hmap : (normSubgroup (NYLL.universeZeroModel F).Carrier
      (NYLL.universeZeroModel E).Carrier).map (e : _ →* _) =
      normSubgroup F.Carrier E.Carrier :=
    NYLL.universeZeroNormRange_map F E
  rw [← hmap, Subgroup.index_map_equiv,
    ClassFieldTheory.Local.normSubgroup_index_eq_finrank (NYLL.universeZeroModel F)
      (NYLL.universeZeroModel E).Carrier]
  exact NYLL.universeZeroAlgebra_finrank F E

end NormIndex

end Langlands.LocalClassField.NormUnitImage
