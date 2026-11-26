import Langlands.MathlibBase

/-! # Gluing characters on a product of subgroups -/

open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uG uC

variable {G : Type uG} [Group G] {C : Type uC} [CommGroup C]

/-- Compatible homomorphisms on two subgroups extend to their product when the
first subgroup normalizes the second and fixes the second homomorphism. -/
theorem exists_monoidHom_of_compatible_restrictions (U D : Subgroup G) (χU : U →* C) (χD : D →* C)
    (hnormal : U ≤ Subgroup.normalizer (D : Set G))
    (hinv : ∀ (u : U) (v : D) (h : (u : G)⁻¹ * (v : G) * u ∈ D),
      χD ⟨_, h⟩ = χD v)
    (hcompat : ∀ g (hU : g ∈ U) (hD : g ∈ D), χU ⟨g, hU⟩ = χD ⟨g, hD⟩) :
    ∃ χ : (U ⊔ D : Subgroup G) →* C,
      (∀ u : U, χ ⟨u, (show U ≤ U ⊔ D from le_sup_left) u.2⟩ = χU u) ∧
      ∀ v : D, χ ⟨v, (show D ≤ U ⊔ D from le_sup_right) v.2⟩ = χD v := by
  classical
  let H := U ⊔ D
  have hex (g : H) : ∃ u : U, ∃ v : D, (u : G) * (v : G) = g := by
    have hg : (g : G) ∈ (H : Set G) := g.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U D hnormal] at hg
    obtain ⟨u, hu, v, hv, heq⟩ := hg
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, heq⟩
  choose u v huv using hex
  let f (g : H) := χU (u g) * χD (v g)
  have hf (g : H) (w : U) (z : D) (hwz : (w : G) * (z : G) = g) : f g = χU w * χD z := by
    let a := (u g)⁻¹ * w
    let b := v g * z⁻¹
    have hval : (a : G) = (b : G) := by
      change ((u g : G)⁻¹ * (w : G)) = (v g : G) * (z : G)⁻¹
      calc _ = (u g : G)⁻¹ * ((w : G) * (z : G)) * (z : G)⁻¹ := by group
           _ = _ := by rw [hwz, ← huv g]; group
    have hab : (⟨(a : G), hval.symm ▸ b.2⟩ : D) = b := Subtype.ext hval
    have hχ : χU a = χD b := (hcompat a a.2 (hval.symm ▸ b.2)).trans (congrArg χD hab)
    have hχ' : (χU (u g))⁻¹ * χU w = χD (v g) * (χD z)⁻¹ := by
      simpa only [a, b, map_mul, map_inv] using hχ
    calc f g = χU (u g) * (χD (v g) * (χD z)⁻¹) * χD z := by simp [f, mul_assoc]
         _ = χU w * χD z := by rw [← hχ']; simp
  let χ : H →* C :=
    { toFun := f
      map_one' := by simpa using hf 1 1 1 (by simp)
      map_mul' g h := by
        have hconj : (u h : G)⁻¹ * (v g : G) * (u h : G) ∈ D :=
          (Subgroup.mem_normalizer_iff''.mp (hnormal (u h).2) (v g)).mp (v g).2
        let v' : D := ⟨_, hconj⟩
        have hprod : ((u g * u h : U) : G) * ((v' * v h : D) : G) = (g * h : H) := by
          change ((u g : G) * (u h : G)) *
            (((u h : G)⁻¹ * (v g : G) * (u h : G)) * (v h : G)) = (g : G) * (h : G)
          rw [← huv g, ← huv h]
          group
        rw [hf (g * h) (u g * u h) (v' * v h) hprod, map_mul, map_mul, hinv (u h) (v g) hconj]
        dsimp [f]
        simp only [mul_assoc, mul_left_comm, mul_comm] }
  refine ⟨χ, fun u' => ?_, fun v' => ?_⟩
  · change f _ = _
    simpa using hf ⟨u', (show U ≤ H from le_sup_left) u'.2⟩ u' 1 (by simp)
  · change f _ = _
    simpa using hf ⟨v', (show D ≤ H from le_sup_right) v'.2⟩ 1 v' (by simp)

end Langlands.BushnellKutzko
