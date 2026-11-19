import Langlands.BushnellKutzko.LatticeChainLayerLift
import Langlands.BushnellKutzko.LatticeChainShifts

/-! # Commutation on successive lattice quotients -/

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

@[simp] theorem stabilizerValuation_one : 𝓛.stabilizerValuation 1 = 0 := by
  have h := 𝓛.stabilizerValuation_mul 1 1
  rw [mul_one] at h
  omega

@[simp] theorem stabilizerValuation_inv (g : 𝓛.stabilizer) :
    𝓛.stabilizerValuation g⁻¹ = -𝓛.stabilizerValuation g := by
  have h := 𝓛.stabilizerValuation_mul g g⁻¹
  rw [mul_inv_cancel, 𝓛.stabilizerValuation_one] at h
  omega

/-- The successive-quotient action of a product is the composite action. -/
theorem stabilizerLayerEquiv_mul_apply (g h : 𝓛.stabilizer) {i j k : ℤ}
    (hh : j = i + 𝓛.stabilizerValuation h) (hg : k = j + 𝓛.stabilizerValuation g)
    (hgh : k = i + 𝓛.stabilizerValuation (g * h)) (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv (g * h) i k hgh q =
      𝓛.stabilizerLayerEquiv g j k hg (𝓛.stabilizerLayerEquiv h i j hh q) := by
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  simp only [stabilizerLayerEquiv_mk]
  rfl

/-- The identity unit acts as the identity on each layer. -/
@[simp] theorem stabilizerLayerEquiv_one_apply {i : ℤ}
    (h : i = i + 𝓛.stabilizerValuation 1) (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv 1 i i h q = q := by
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rw [stabilizerLayerEquiv_mk, intervalMk_eq_iff]
  change (1 : Module.End K V) v - v ∈ 𝓛.lattice (i + 1)
  simp

/-- Two units with product one give inverse layer maps. -/
theorem stabilizerLayerEquiv_cancel_apply (g h : 𝓛.stabilizer) {i j : ℤ} (hgh : g * h = 1)
    (hh : j = i + 𝓛.stabilizerValuation h) (hg : i = j + 𝓛.stabilizerValuation g)
    (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv g j i hg (𝓛.stabilizerLayerEquiv h i j hh q) = q := by
  have hshift : i = i + 𝓛.stabilizerValuation (g * h) := by rw [hgh, stabilizerValuation_one, add_zero]
  have hone (a : 𝓛.stabilizer) (ha : a = 1) (hs : i = i + 𝓛.stabilizerValuation a) :
      𝓛.stabilizerLayerEquiv a i i hs q = q := by
    subst a
    exact 𝓛.stabilizerLayerEquiv_one_apply hs q
  exact (𝓛.stabilizerLayerEquiv_mul_apply g h hh hg hshift q).symm.trans
    (hone (g * h) hgh hshift)

/-- Units intertwining a family of successive-quotient endomorphisms form a subgroup. -/
def layerCommutingSubgroup (D : ∀ i : ℤ, Module.End O (𝓛.Layer i)) : Subgroup 𝓛.stabilizer where
  carrier := {g | 𝓛.LayerFamilyCommutes D g}
  one_mem' := by
    intro i j h
    have hij : j = i := by simpa only [stabilizerValuation_one, add_zero] using h
    revert h
    subst j
    intro h q
    change 𝓛.stabilizerLayerEquiv 1 i i h (D i q) = D i (𝓛.stabilizerLayerEquiv 1 i i h q)
    rw [𝓛.stabilizerLayerEquiv_one_apply, 𝓛.stabilizerLayerEquiv_one_apply]
  mul_mem' := by
    intro g h hg hh i k hk q
    let j := i + 𝓛.stabilizerValuation h
    have hhk : k = j + 𝓛.stabilizerValuation g := by
      rw [𝓛.stabilizerValuation_mul] at hk
      dsimp [j]
      omega
    rw [𝓛.stabilizerLayerEquiv_mul_apply g h (j := j) rfl hhk hk,
      hh i j rfl,
      hg j k hhk,
      𝓛.stabilizerLayerEquiv_mul_apply g h (j := j) rfl hhk hk]
  inv_mem' := by
    intro g hg i j hij q
    have hji : i = j + 𝓛.stabilizerValuation g := by
      rw [𝓛.stabilizerValuation_inv] at hij
      omega
    apply (𝓛.stabilizerLayerEquiv g j i hji).injective
    change 𝓛.stabilizerLayerEquiv g j i hji
        (𝓛.stabilizerLayerEquiv g⁻¹ i j hij (D i q)) =
      𝓛.stabilizerLayerEquiv g j i hji (D j (𝓛.stabilizerLayerEquiv g⁻¹ i j hij q))
    have hcancel := 𝓛.stabilizerLayerEquiv_cancel_apply g g⁻¹ (mul_inv_cancel g) hij hji
    rw [hcancel, hg j i hji, hcancel]

/-- Intertwining the layer action of an order element is equivalent to an extra
filtration step in its commutator with the shifting unit. -/
theorem layerAction_commutes_iff (x : 𝓛.order) (g : 𝓛.stabilizer) :
    𝓛.LayerFamilyCommutes (𝓛.layerAction x) g ↔
      adjointMap O (g.val : Module.End K V) x.val ∈
        𝓛.endFiltration (𝓛.stabilizerValuation g + 1) := by
  constructor
  · intro h i v hv
    let j := i + 𝓛.stabilizerValuation g
    have heq := h i j rfl (𝓛.intervalMk i (i + 1) v hv)
    simp only [layerAction_mk, stabilizerLayerEquiv_mk, intervalMk_eq_iff] at heq
    change (g.val : Module.End K V) (x.val v) - x.val ((g.val : Module.End K V) v) ∈
      𝓛.lattice (i + (𝓛.stabilizerValuation g + 1))
    rw [← add_assoc]
    exact heq
  · intro h i j hij q
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    simp only [layerAction_mk, stabilizerLayerEquiv_mk, intervalMk_eq_iff]
    rw [hij, add_assoc]
    exact h i v hv

/-- Exact commutation implies commutation on the successive quotients. -/
theorem layerAction_commutes_of_commute (x : 𝓛.order) (g : 𝓛.stabilizer)
    (h : Commute (g.val : Module.End K V) x.val) :
    𝓛.LayerFamilyCommutes (𝓛.layerAction x) g := by
  apply (𝓛.layerAction_commutes_iff x g).mpr
  change (g.val : Module.End K V) * x.val - x.val * (g.val : Module.End K V) ∈ _
  rw [h.eq, sub_self]
  exact zero_mem _

/-- The scalar periodicity of every order element follows from field linearity. -/
theorem layerAction_commutes_uniformizer [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O K] {π : O} (hπ : Irreducible π) (x : 𝓛.order) :
    𝓛.LayerFamilyCommutes (𝓛.layerAction x) (𝓛.uniformizerStabilizer hπ) := by
  apply 𝓛.layerAction_commutes_of_commute
  ext v
  simp only [Module.End.mul_apply, uniformizerStabilizer_apply, map_smul]

end Langlands.BushnellKutzko.LatticeChain
