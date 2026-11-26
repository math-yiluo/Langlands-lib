import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesStatement

/-! # Comparing unit-group indices with additive layer indices -/

noncomputable section
open ValuativeRel

namespace Langlands.BushnellKutzko

universe uA uF uV

section Units

variable {A : Type uA} [Ring A]
  (J : Subgroup Aˣ) (P Q : AddSubgroup A) (hQP : Q ≤ P)
  (hJ : ∀ g : J, ((g : Aˣ) : A) - 1 ∈ P)
  (hmul : ∀ x ∈ P, ∀ y ∈ P, x * y ∈ Q)

/-- Reduction of `g - 1` modulo an additive subgroup containing the products of
all differences. -/
def unitSubOneQuotient : J →* Multiplicative (P ⧸ Q.comap P.subtype) where
  toFun g := Multiplicative.ofAdd (QuotientAddGroup.mk' _ ⟨_, hJ g⟩)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change QuotientAddGroup.mk' (Q.comap P.subtype) (⟨(1 : A) - 1, hJ 1⟩ : P) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    simpa only [AddSubgroup.mem_comap, AddSubgroup.coe_subtype, sub_self] using Q.zero_mem
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    let q := QuotientAddGroup.mk' (Q.comap P.subtype)
    let x : P := ⟨((g : Aˣ) : A) - 1, hJ g⟩
    let y : P := ⟨((h : Aˣ) : A) - 1, hJ h⟩
    let z : P := ⟨(x : A) * (y : A), hQP (hmul _ x.property _ y.property)⟩
    have hxy : (⟨(((g * h : J) : Aˣ) : A) - 1, hJ (g * h)⟩ : P) = x + y + z := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Units.val_mul, AddSubgroup.coe_add, x, y, z]
      noncomm_ring
    have hz : q z = 0 := (QuotientAddGroup.eq_zero_iff z).mpr (hmul _ x.property _ y.property)
    change q ⟨_, hJ (g * h)⟩ = q x + q y
    rw [hxy, map_add, map_add, hz, add_zero]

include hQP hJ hmul in
/-- When `g - 1` runs over `P`, and membership in `H` is reduction to zero modulo
`Q`, the multiplicative and additive indices agree. -/
theorem relIndex_eq_of_sub_one (H : Subgroup Aˣ)
    (hH : ∀ g : J, (g : Aˣ) ∈ H ↔ ((g : Aˣ) : A) - 1 ∈ Q)
    (hsurj : ∀ x ∈ P, ∃ g : J, ((g : Aˣ) : A) - 1 = x) :
    H.relIndex J = Q.relIndex P := by
  let f := unitSubOneQuotient J P Q hQP hJ hmul
  have hker : f.ker = H.subgroupOf J := by
    ext g
    change f g = 1 ↔ (g : Aˣ) ∈ H
    rw [hH]
    change QuotientAddGroup.mk' (Q.comap P.subtype) (⟨_, hJ g⟩ : P) = 0 ↔ _
    exact QuotientAddGroup.eq_zero_iff _
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective (Q.comap P.subtype) w.toAdd
    obtain ⟨g, hg⟩ := hsurj x x.property
    refine ⟨g, Multiplicative.toAdd.injective ?_⟩
    change QuotientAddGroup.mk' (Q.comap P.subtype) (⟨_, hJ g⟩ : P) = w.toAdd
    rw [show (⟨_, hJ g⟩ : P) = x from Subtype.ext hg, hx]
  change (H.subgroupOf J).index = Nat.card (P ⧸ Q.comap P.subtype)
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  rfl

/-- Conjugation on the additive group of a ring by a unit. -/
def unitConjAddEquiv (g : Aˣ) : A ≃+ A where
  toFun x := (g : A) * x * ((g⁻¹ : Aˣ) : A)
  invFun x := ((g⁻¹ : Aˣ) : A) * x * (g : A)
  left_inv x := by
    calc
      _ = (((g⁻¹ : Aˣ) : A) * (g : A)) * x * (((g⁻¹ : Aˣ) : A) * (g : A)) := by
        simp only [mul_assoc]
      _ = x := by rw [Units.inv_mul, one_mul, mul_one]
  right_inv x := by
    calc
      _ = ((g : A) * ((g⁻¹ : Aˣ) : A)) * x * ((g : A) * ((g⁻¹ : Aˣ) : A)) := by
        simp only [mul_assoc]
      _ = x := by rw [Units.mul_inv, one_mul, mul_one]
  map_add' x y := by simp only [mul_add, add_mul]

theorem unitConjAddEquiv_mul (g : Aˣ) (x y : A) :
    unitConjAddEquiv g (x * y) = unitConjAddEquiv g x * unitConjAddEquiv g y := by
  change (g : A) * (x * y) * ((g⁻¹ : Aˣ) : A) =
    ((g : A) * x * ((g⁻¹ : Aˣ) : A)) * ((g : A) * y * ((g⁻¹ : Aˣ) : A))
  rw [mul_assoc ((g : A) * x) _, ← mul_assoc ((g⁻¹ : Aˣ) : A),
    ← mul_assoc ((g⁻¹ : Aˣ) : A), Units.inv_mul, one_mul]
  simp only [mul_assoc]

theorem unitConjAddEquiv_sub_one (g h : Aˣ) :
    unitConjAddEquiv g ((h : A) - 1) = ((g * h * g⁻¹ : Aˣ) : A) - 1 := by
  change (g : A) * ((h : A) - 1) * ((g⁻¹ : Aˣ) : A) = _
  rw [mul_sub, sub_mul, mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]

end Units

section Layers

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem one_mem_simpleStratumLattices (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) :
    (1 : A) ∈ simpleHLattice L n β tail ∧ (1 : A) ∈ simpleJLattice L n β tail := by
  have hc : (1 : A) ∈ centralizerLattice L β 0 :=
    ⟨L.mem_order_iff_mem_endFiltration.mp (one_mem L.order), by
      change adjointMap 𝒪[F] β 1 = 0
      simp [adjointMap]⟩
  cases tail <;> exact ⟨Submodule.mem_sup_left hc, Submodule.mem_sup_left hc⟩

/-- On the positive-depth common domain the relative group index is the index
of the two additive layer intersections. -/
theorem simpleStratum_relIndex_intertwiningDomain
    (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (y : G) :
    let H := simpleHGroup S.chain S.n S.b q.tail 1
    let J := simpleJGroup S.chain S.n S.b q.tail 1
    let h := (simpleHLayer S.chain S.n S.b q.tail 1).toAddSubgroup
    let j := (simpleJLayer S.chain S.n S.b q.tail 1).toAddSubgroup
    let a := (unitConjAddEquiv y).toAddMonoidHom
    (intertwiningDomain H H y).relIndex (intertwiningDomain J J y) =
      (h.comap a ⊓ h).relIndex (j.comap a ⊓ j) := by
  intro H J h j a
  have hg := (hgroups F V S hr hs q).1 1
  have hl := hlattices F V S hr hs q
  let L := S.chain
  obtain ⟨hHone, hJone⟩ := one_mem_simpleStratumLattices L S.n S.b q.tail
  have hP : ∀ x : G, x ∈ H ↔ (x : A) - 1 ∈ h := by
    intro x
    change x ∈ (H : Set G) ↔ _
    rw [hg.1]
    constructor
    · intro hx
      exact ⟨sub_mem hx.2 hHone, hx.1.2.2⟩
    · intro hx
      have hx₁ := hx.2
      obtain ⟨u, hu, heq⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl hx₁
      have hux : u = x := Units.ext (by rw [heq]; abel)
      refine ⟨hux ▸ hu, ?_⟩
      have hh := add_mem hx.1 hHone
      rwa [sub_add_cancel] at hh
  have hQ : ∀ x : G, x ∈ J ↔ (x : A) - 1 ∈ j := by
    intro x
    change x ∈ (J : Set G) ↔ _
    rw [hg.2]
    constructor
    · intro hx
      exact ⟨sub_mem hx.2 hJone, hx.1.2.2⟩
    · intro hx
      obtain ⟨u, hu, heq⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl hx.2
      have hux : u = x := Units.ext (by rw [heq]; abel)
      refine ⟨hux ▸ hu, ?_⟩
      have hh := add_mem hx.1 hJone
      rwa [sub_add_cancel] at hh
  have hle : h ≤ j := (hl.2.1.2.2.2.2.2.2.2 1).2.2
  have hprod {x x' : A} (hx : x ∈ j) (hx' : x' ∈ j) : x * x' ∈ h := by
    have hh := hl.2.2.2.2.1.2.1 1 1 le_rfl le_rfl
      (Submodule.mul_mem_mul hx hx')
    exact ⟨hh.1, L.endFiltration_antitone (by norm_num) hh.2⟩
  have commonH (g : G) : g ∈ intertwiningDomain H H y ↔ (g : A) - 1 ∈ h.comap a ⊓ h := by
    rw [mem_intertwiningDomain, hP, hP]
    change _ ↔ unitConjAddEquiv y ((g : A) - 1) ∈ h ∧ (g : A) - 1 ∈ h
    rw [unitConjAddEquiv_sub_one]
  have commonJ (g : G) : g ∈ intertwiningDomain J J y ↔ (g : A) - 1 ∈ j.comap a ⊓ j := by
    rw [mem_intertwiningDomain, hQ, hQ]
    change _ ↔ unitConjAddEquiv y ((g : A) - 1) ∈ j ∧ (g : A) - 1 ∈ j
    rw [unitConjAddEquiv_sub_one]
  apply relIndex_eq_of_sub_one _ _ _ (inf_le_inf (AddSubgroup.comap_mono hle) hle)
    (fun g => (commonJ g).mp g.property) _ _ (fun g => commonH g)
  · intro x hx
    obtain ⟨g, -, hval⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl hx.2.2
    have hdiff : (g : A) - 1 = x := by rw [hval]; abel
    exact ⟨⟨g, (commonJ g).mpr (hdiff.symm ▸ hx)⟩, hdiff⟩
  · intro x hx x' hx'
    refine ⟨?_, hprod hx.2 hx'.2⟩
    change unitConjAddEquiv y (x * x') ∈ h
    rw [unitConjAddEquiv_mul]
    exact hprod hx.1 hx'.1

end Layers

end Langlands.BushnellKutzko
