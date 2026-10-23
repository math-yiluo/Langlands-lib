import Langlands.Cohomology.SylowDetectionStatement
import Langlands.Cohomology.Tate.PositiveRestriction
import Mathlib.GroupTheory.Sylow

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Cohomology

set_option backward.isDefEq.respectTransparency false

section Pointwise

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- A vanishing subgroup restriction annihilates the class by the subgroup index. -/
theorem index_nsmul_eq_zero_of_restriction_eq_zero (A : Rep.{u} k G)
    (H : Subgroup G) (n : ℕ) [NeZero n] (x : groupCohomology A n)
    (hx : groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n x = 0) :
    H.index • x = 0 := by
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let e := ((TateCohomology.isoGroupCohomology n).app A).toLinearEquiv
  let eH := ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).toLinearEquiv
  have hr : Langlands.Tate.restriction H A n (e.symm x) = 0 := by
    change (ModuleCat.ofHom (Langlands.Tate.restriction H A n)) (e.symm x) = 0
    rw [Langlands.Tate.restriction_groupCohomology]
    change eH.symm (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n
      (e (e.symm x))) = 0
    rw [e.apply_symm_apply, hx, map_zero]
  have hz : H.index • e.symm x = 0 := by
    rw [← Langlands.Tate.corestriction_restriction H A n, hr, map_zero]
  simpa only [map_nsmul, e.apply_symm_apply, map_zero] using congrArg e hz

/-- All Sylow restrictions jointly detect a positive-degree ordinary cohomology class. -/
theorem eq_zero_of_sylow_restriction_eq_zero (A : Rep.{u} k G) (n : ℕ) [NeZero n]
    (x : groupCohomology A n)
    (hx : ∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) n x = 0) :
    x = 0 := by
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpx
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  have hidx : P.1.index • x = 0 :=
    index_nsmul_eq_zero_of_restriction_eq_zero A P.1 n x (hx p hp P)
  exact P.not_dvd_index (hpx.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hidx))

/-- If every Sylow subgroup has zero cohomology, the whole finite group does too. -/
theorem subsingleton_of_sylow (A : Rep.{u} k G) (n : ℕ) [NeZero n]
    (h : ∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      Subsingleton (groupCohomology (Rep.res P.1.subtype A) n)) :
    Subsingleton (groupCohomology A n) := by
  refine ⟨fun x y => ?_⟩
  have hz (x : groupCohomology A n) : x = 0 := by
    apply eq_zero_of_sylow_restriction_eq_zero A n x
    intro p hp P
    let := h p hp P
    exact Subsingleton.elim _ _
  rw [hz x, hz y]

end Pointwise

/-- Positive-degree ordinary group cohomology is detected by Sylow restrictions. -/
theorem sylowDetection : SylowDetection.{u} := by
  intro k _ G _ _ A n hn x hx
  have : NeZero n := ⟨hn.ne'⟩
  exact eq_zero_of_sylow_restriction_eq_zero A n x hx

/-- Subsingleton Sylow cohomology forces subsingleton positive-degree cohomology. -/
theorem sylowSubsingleton : SylowSubsingleton.{u} := by
  intro k _ G _ _ A n hn h
  have : NeZero n := ⟨hn.ne'⟩
  exact subsingleton_of_sylow A n h

end Langlands.Cohomology
