import Langlands.Cohomology.PrimeSectionH1Statement
import Langlands.Cohomology.SylowDetectionProof
import Mathlib.GroupTheory.Nilpotent

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Cohomology


section Pointwise

variable {k G : Type u} [CommRing k] [Group G]

/-- Inflation-restriction propagates H1 vanishing through a normal subgroup. -/
theorem h1_subsingleton_of_normal (A : Rep.{u} k G) (N : Subgroup G) [N.Normal]
    (hN : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (hQ : Subsingleton (groupCohomology (A.quotientToInvariants N) 1)) :
    Subsingleton (groupCohomology A 1) := by
  let := hN
  let := hQ
  apply ModuleCat.subsingleton_of_isZero
  apply (groupCohomology.H1InfRes_exact A N).isZero_X₂
  · exact (ModuleCat.isZero_of_subsingleton
      (groupCohomology (A.quotientToInvariants N) 1)).eq_of_src _ _
  · exact (ModuleCat.isZero_of_subsingleton
      (groupCohomology (Rep.res N.subtype A) 1)).eq_of_tgt _ _

/-- Nested restriction and restriction to the image subgroup have isomorphic H1. -/
theorem h1_subsingleton_nested (A : Rep.{u} k G) (H : Subgroup G)
    (N : Subgroup H)
    (h : Subsingleton (groupCohomology (Rep.res (N.map H.subtype).subtype A) 1)) :
    Subsingleton (groupCohomology (Rep.res N.subtype (Rep.res H.subtype A)) 1) := by
  let := h
  let e := N.equivMapOfInjective H.subtype H.subtype_injective
  let i := groupCohomology.mapIso
    (A := Rep.res (N.map H.subtype).subtype A)
    (B := Rep.res N.subtype (Rep.res H.subtype A))
    e (LinearEquiv.refl k A.V) (fun _ => by rfl) 1
  exact i.toLinearEquiv.injective.subsingleton

/-- Prime-order normal sections suffice for H1 vanishing in a finite group. -/
theorem primeSectionH1Vanishing_of_sections [Finite G] (A : Rep.{u} k G)
    (h : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      N.index.Prime →
      Subsingleton (groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 1)) :
    Subsingleton (groupCohomology A 1) := by
  have hpSub (p : ℕ) [Fact p.Prime] (H : Subgroup G) (hH : IsPGroup p H) :
      Subsingleton (groupCohomology (Rep.res H.subtype A) 1) := by
    induction hm : Nat.card H using Nat.strong_induction_on generalizing H with
    | h m ih =>
      rcases hH.card_eq_or_dvd with h1 | hpdiv
      · let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1).1
        exact ModuleCat.subsingleton_of_isZero
          (isZero_groupCohomology_succ_of_subsingleton _ 0)
      · let : Group.IsNilpotent H := hH.isNilpotent
        obtain ⟨N, hidx, hnormal⟩ :=
          Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hpdiv
        let := hnormal
        have hlt : Nat.card (N.map H.subtype) < m := by
          rw [← hm, Subgroup.card_map_of_injective H.subtype_injective,
            ← N.card_mul_index, hidx]
          exact lt_mul_of_one_lt_right Nat.card_pos (Fact.out : p.Prime).one_lt
        have hK : IsPGroup p (N.map H.subtype) :=
          (hH.to_subgroup N).of_equiv (N.equivMapOfInjective H.subtype H.subtype_injective)
        have hsmall := ih _ hlt (N.map H.subtype) hK rfl
        apply h1_subsingleton_of_normal (Rep.res H.subtype A) N
        · exact h1_subsingleton_nested A H N hsmall
        · exact h H N (hidx ▸ (Fact.out : p.Prime))
  apply sylowSubsingleton k G A 1 Nat.one_pos
  intro p hp P
  let : Fact p.Prime := ⟨hp⟩
  exact hpSub p P.1 P.isPGroup'

end Pointwise

/-- H1 vanishing of a finite group follows from vanishing on prime-index normal sections. -/
theorem primeSectionH1Vanishing : PrimeSectionH1Vanishing.{u} := by
  intro k _ G _ _ A h
  exact primeSectionH1Vanishing_of_sections A h

end Langlands.Cohomology
