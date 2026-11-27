import Langlands.MathlibBase

/-! # Descent of a character evaluated on commutators -/

open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uG uC

variable {G : Type uG} [Group G] {C : Type uC} [CommGroup C]

/-- A character evaluated on commutators gives a nondegenerate alternating form
on `J/H` if commutators lie in `H` and the elements annihilating all commutators
under the character are precisely the elements of `H`. -/
theorem exists_quotientCommutatorPairing {H J : Subgroup G}
    (hHJ : H ≤ J) (θ : H →* C)
    (hcomm : ∀ x y : J, ⁅(x : G), (y : G)⁆ ∈ H)
    (hrad : ∀ x : J, (∀ y : J, θ ⟨_, hcomm x y⟩ = 1) ↔ (x : G) ∈ H) :
    let N := H.comap J.subtype
    ∃ hN : N.Normal,
      letI := hN
      let Q := J ⧸ N
      let π := QuotientGroup.mk' N
      ∃ B : Q →* (Q →* C),
        (∀ x y : J, B (π x) (π y) = θ ⟨_, hcomm x y⟩) ∧
        (∀ x : Q, B x x = 1) ∧
        (∀ x : Q, (∀ y : Q, B x y = 1) → x = 1) := by
  let N := H.comap J.subtype
  let c (x y : J) : H := ⟨_, hcomm x y⟩
  have hconj (x : J) (h : H) : (x : G) * (h : G) * (x : G)⁻¹ ∈ H := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    exact H.mul_mem (hcomm x ⟨h, hHJ h.property⟩) h.property
  let hN : N.Normal := ⟨fun x hx y => hconj y ⟨x, hx⟩⟩
  refine ⟨hN, ?_⟩
  have hright (x y : J) (hy : (y : G) ∈ H) : θ (c x y) = 1 := by
    have heq : c x y = (c y x)⁻¹ := Subtype.ext (commutatorElement_inv _ _).symm
    rw [heq, map_inv, (hrad y).mpr hy x, inv_one]
  let conj (x : J) (h : H) : H := ⟨_, hconj x h⟩
  have hconjVal (x : J) (h : H) : θ (conj x h) = θ h := by
    let y : J := ⟨h, hHJ h.property⟩
    have heq : conj x h = c x y * h := Subtype.ext (by
      change MulAut.conj (x : G) (h : G) = _
      exact conj_eq_commutatorElement_mul)
    rw [heq, map_mul, hright x y h.property, one_mul]
  have hone (x : J) : c x 1 = 1 := Subtype.ext (commutatorElement_one_right _)
  have hmul_right (x y z : J) : c x (y * z) = c x y * conj y (c x z) :=
    Subtype.ext (by
      change ⁅(x : G), (y : G) * (z : G)⁆ =
        ⁅(x : G), (y : G)⁆ * ((y : G) * ⁅(x : G), (z : G)⁆ * (y : G)⁻¹)
      simp only [commutatorElement_mul_right_eq_mul_conj, mul_assoc])
  have hmul_left (x y z : J) : c (x * y) z = conj x (c y z) * c x z :=
    Subtype.ext (commutatorElement_mul_left_eq_conj_mul _ _ _)
  let e (x : J) : J →* C :=
    { toFun := fun y => θ (c x y)
      map_one' := by rw [hone, map_one]
      map_mul' := fun y z => by rw [hmul_right, map_mul, hconjVal] }
  let Q := J ⧸ N
  let π := QuotientGroup.mk' N
  let eQ (x : J) : Q →* C := QuotientGroup.lift N (e x) (hright x)
  have heQ (x y : J) : eQ x (π y) = θ (c x y) := rfl
  let E : J →* (Q →* C) :=
    { toFun := eQ
      map_one' := by
        apply MonoidHom.ext
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
        have h : c 1 y = 1 := Subtype.ext (commutatorElement_one_left _)
        change eQ 1 (π y) = 1
        rw [heQ, h, map_one]
      map_mul' := fun x y => by
        apply MonoidHom.ext
        intro q
        obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N q
        change eQ (x * y) (π z) = eQ x (π z) * eQ y (π z)
        rw [heQ, heQ, heQ, hmul_left, map_mul, hconjVal, mul_comm] }
  have hE : N ≤ E.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply MonoidHom.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    change eQ x (π y) = 1
    rw [heQ]
    exact (hrad x).mpr hx y
  let B := QuotientGroup.lift N E hE
  have hB (x y : J) : B (π x) (π y) = θ (c x y) := heQ x y
  refine ⟨B, hB, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have h : c x x = 1 := Subtype.ext (commutatorElement_self _)
    rw [hB, h, map_one]
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (hrad x).mp fun y => (hB x y).symm.trans (hq (π y))

end Langlands.BushnellKutzko
