import Langlands.BushnellKutzko.LatticeChainLayerCommutation

/-! # The indicator family for multiples of a layer index -/

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- Identity on layers indexed by multiples of `m` and zero on the other layers. -/
def layerIndicator (m : ℤ) (i : ℤ) : Module.End O (𝓛.Layer i) :=
  if m ∣ i then LinearMap.id else 0

/-- A unit intertwines the indicator family exactly when its shift is divisible by `m`. -/
theorem layerIndicator_commutes_iff (m : ℤ) (g : 𝓛.stabilizer) :
    𝓛.LayerFamilyCommutes (𝓛.layerIndicator m) g ↔ m ∣ 𝓛.stabilizerValuation g := by
  constructor
  · intro h
    by_contra hn
    have := 𝓛.layer_nontrivial 0
    obtain ⟨q, hq⟩ := exists_ne (0 : 𝓛.Layer 0)
    let j := 𝓛.stabilizerValuation g
    have hj : j = 0 + 𝓛.stabilizerValuation g := by simp [j]
    have he := h 0 j hj q
    change ¬ m ∣ j at hn
    have hz : 𝓛.layerIndicator m j = 0 := by simp [layerIndicator, hn]
    have hid : 𝓛.layerIndicator m 0 = LinearMap.id := by simp [layerIndicator]
    rw [hz, hid, LinearMap.id_apply, LinearMap.zero_apply] at he
    exact hq ((𝓛.stabilizerLayerEquiv g 0 j hj).injective (he.trans (map_zero _).symm))
  · intro hm i j hj q
    have hd : m ∣ j ↔ m ∣ i := hj ▸ dvd_add_left hm
    by_cases hi : m ∣ i
    · simp [layerIndicator, hi, hd.mpr hi]
    · have hj' : ¬ m ∣ j := fun hc => hi (hd.mp hc)
      simp [layerIndicator, hi, hj']

end Langlands.BushnellKutzko.LatticeChain
