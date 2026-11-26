import Langlands.BushnellKutzko.NonsplitFundamentalSimpleStatement
import Langlands.BushnellKutzko.LatticeChainLayerCommutation
import Langlands.BushnellKutzko.CriticalDerivedNormalization
import Langlands.BushnellKutzko.NonsplitFundamentalSimpleAlgebra

/-! # Layer actions and families transported along a translation

The order `𝔄(𝓛)` acts on each layer `L_i / L_{i+1}` (`layerHom`), and the action factors
through `𝔄/𝔓` (`residueLayerHom`). For a translation `t` of the chain of positive shift `g`,
`extendFamily` extends endomorphisms of the layers at `0 ≤ r < g` to all indices by transport
along powers of `t`; the result commutes with `t`, and with every translation of shift zero
commuting with `t` whose action the given endomorphisms commute with. A family commuting with
`t` vanishes if it vanishes at `0 ≤ r < g` (`eq_zero_of_commutes`).
-/

noncomputable section

open Polynomial

namespace Langlands.BushnellKutzko.NonsplitSimple

open LatticeChain CriticalDerived

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-! ### The action of the order on one layer -/

/-- The action of `𝔄(𝓛)` on the layer `L_i / L_{i+1}`, as an algebra homomorphism. -/
def layerHom (i : ℤ) : 𝓛.order →ₐ[O] Module.End O (𝓛.Layer i) where
  toFun x := 𝓛.layerAction x i
  map_one' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    rfl
  map_mul' x y := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    rfl
  map_zero' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    rfl
  map_add' x y := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    rfl
  commutes' a := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
    change 𝓛.intervalMk i (i + 1) ((algebraMap O (Module.End K V) a) v) _ =
      a • 𝓛.intervalMk i (i + 1) v hv
    simp only [Module.algebraMap_end_apply]
    rfl

@[simp] theorem layerHom_apply (i : ℤ) (x : 𝓛.order) : layerHom 𝓛 i x = 𝓛.layerAction x i :=
  rfl

/-- An element of the order acts by zero on every layer exactly when it lies in `𝔓`. -/
theorem layerAction_eq_zero_iff (x : 𝓛.order) :
    (∀ i, 𝓛.layerAction x i = 0) ↔ x ∈ 𝓛.firstFiltrationIdeal := by
  have h := 𝓛.layerAction_eq_iff x 0
  have h0 : ∀ i, 𝓛.layerAction (0 : 𝓛.order) i = 0 := fun i => map_zero (layerHom 𝓛 i)
  simp only [ZeroMemClass.coe_zero, sub_zero, h0] at h
  exact h

/-- The action of `𝔄/𝔓` on one layer. -/
def residueLayerHom (i : ℤ) : 𝓛.order ⧸ 𝓛.firstFiltrationIdeal →+* Module.End O (𝓛.Layer i) :=
  Ideal.Quotient.lift _ (layerHom 𝓛 i).toRingHom
    (fun x hx => (layerAction_eq_zero_iff 𝓛 x).mpr hx i)

@[simp] theorem residueLayerHom_mk (i : ℤ) (x : 𝓛.order) :
    residueLayerHom 𝓛 i (Ideal.Quotient.mk _ x) = 𝓛.layerAction x i :=
  rfl

/-! ### Shifts of powers -/

/-- The shift of an integer power of a translation of the chain. -/
theorem stabilizerValuation_zpow (g : 𝓛.stabilizer) (n : ℤ) :
    𝓛.stabilizerValuation (g ^ n) = n * 𝓛.stabilizerValuation g := by
  have h := (Shifts.of_stabilizer (𝓛 := 𝓛) g).zpow n
  have hg : (⟨(g.val ^ n : (Module.End K V)ˣ), h.mem_stabilizer⟩ : 𝓛.stabilizer) = g ^ n :=
    Subtype.ext (by simp)
  rw [← hg]
  exact h.stabilizerValuation_eq

/-- A stabilizer element of shift zero lies in the order. -/
theorem mem_order_of_shift_zero (g : 𝓛.stabilizer) (hg : 𝓛.stabilizerValuation g = 0) :
    ((g.val : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order := by
  have h := (Shifts.of_stabilizer (𝓛 := 𝓛) g).1
  rw [hg] at h
  exact h

/-- On a layer, a stabilizer element of shift zero acts as the corresponding order element. -/
theorem stabilizerLayerEquiv_eq_layerAction (g : 𝓛.stabilizer)
    (hg : 𝓛.stabilizerValuation g = 0) (i : ℤ) (h : i = i + 𝓛.stabilizerValuation g)
    (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv g i i h q =
      𝓛.layerAction ⟨_, mem_order_of_shift_zero 𝓛 g hg⟩ i q := by
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rfl

/-- The layer map of a translation depends only on the translation. -/
theorem stabilizerLayerEquiv_congr {s s' : 𝓛.stabilizer} (hs : s = s') {i j : ℤ}
    (h : j = i + 𝓛.stabilizerValuation s) (h' : j = i + 𝓛.stabilizerValuation s')
    (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv s i j h q = 𝓛.stabilizerLayerEquiv s' i j h' q := by
  subst hs
  rfl

/-! ### Families determined by one period of a shifting element -/

section Extend

variable (t : 𝓛.stabilizer) {g : ℕ} (hg : 0 < g) (ht : 𝓛.stabilizerValuation t = g)

include ht in
/-- Every index is reached from its residue modulo `g` by a power of `t`. -/
theorem index_eq (i : ℤ) : i = i % g + 𝓛.stabilizerValuation (t ^ (i / (g : ℤ))) := by
  rw [stabilizerValuation_zpow, ht]
  have := Int.emod_add_mul_ediv i g
  linarith

/-- Transport of an endomorphism of the layer at `a` to the layer at `i` by `s`. -/
def conjLayer (s : 𝓛.stabilizer) {a i : ℤ} (h : i = a + 𝓛.stabilizerValuation s)
    (f : Module.End O (𝓛.Layer a)) : Module.End O (𝓛.Layer i) :=
  (𝓛.stabilizerLayerEquiv s a i h).toLinearMap ∘ₗ f ∘ₗ
    (𝓛.stabilizerLayerEquiv s a i h).symm.toLinearMap

/-- Transport of a family member depends only on the indices and the translation. -/
theorem conjLayer_congr (c : ∀ r : ℤ, Module.End O (𝓛.Layer r)) {a a' i : ℤ}
    {s s' : 𝓛.stabilizer} (ha : a = a') (hs : s = s') (h : i = a + 𝓛.stabilizerValuation s)
    (h' : i = a' + 𝓛.stabilizerValuation s') :
    conjLayer 𝓛 s h (c a) = conjLayer 𝓛 s' h' (c a') := by
  subst ha
  subst hs
  rfl

/-- The family obtained from its values on `0 ≤ r < g` by transport along powers of `t`. -/
def extendFamily (c : ∀ r : ℤ, Module.End O (𝓛.Layer r)) (i : ℤ) : Module.End O (𝓛.Layer i) :=
  conjLayer 𝓛 (t ^ (i / (g : ℤ))) (index_eq 𝓛 t ht i) (c (i % g))

/-- The extended family agrees with the given family on `0 ≤ r < g`. -/
theorem extendFamily_of_mem (c : ∀ r : ℤ, Module.End O (𝓛.Layer r)) {r : ℤ} (hr₀ : 0 ≤ r)
    (hr : r < g) : extendFamily 𝓛 t ht c r = c r := by
  have hmod : r % (g : ℤ) = r := Int.emod_eq_of_lt hr₀ hr
  have hdiv : r / (g : ℤ) = 0 := Int.ediv_eq_zero_of_lt hr₀ hr
  have h1 : r = r + 𝓛.stabilizerValuation 1 := by simp
  rw [extendFamily, conjLayer_congr 𝓛 c hmod (show t ^ (r / (g : ℤ)) = 1 by rw [hdiv, zpow_zero])
    _ h1]
  refine LinearMap.ext fun q => ?_
  simp only [conjLayer, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  have hq : (𝓛.stabilizerLayerEquiv 1 r r h1).symm q = q := by
    rw [LinearEquiv.symm_apply_eq, 𝓛.stabilizerLayerEquiv_one_apply]
  rw [hq, 𝓛.stabilizerLayerEquiv_one_apply]

include hg in
/-- The extended family commutes with `t`. -/
theorem extendFamily_commutes (c : ∀ r : ℤ, Module.End O (𝓛.Layer r)) :
    𝓛.LayerFamilyCommutes (extendFamily 𝓛 t ht c) t := by
  intro i j hij q
  have hji : j = i + g := by rw [hij, ht]
  have hmod : j % (g : ℤ) = i % (g : ℤ) := by rw [hji, Int.add_emod_right]
  have hdiv : t ^ (j / (g : ℤ)) = t * t ^ (i / (g : ℤ)) := by
    rw [hji, Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self (by exact_mod_cast hg.ne'),
      add_comm, zpow_add, zpow_one]
  have hshift : j = i % (g : ℤ) + 𝓛.stabilizerValuation (t * t ^ (i / (g : ℤ))) := by
    have := index_eq 𝓛 t ht i
    rw [𝓛.stabilizerValuation_mul, hij]
    linarith
  rw [extendFamily, extendFamily, conjLayer_congr 𝓛 c hmod hdiv _ hshift]
  simp only [conjLayer, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  have hsymm : (𝓛.stabilizerLayerEquiv (t * t ^ (i / (g : ℤ))) (i % (g : ℤ)) j hshift).symm
      (𝓛.stabilizerLayerEquiv t i j hij q) =
      (𝓛.stabilizerLayerEquiv (t ^ (i / (g : ℤ))) (i % (g : ℤ)) i (index_eq 𝓛 t ht i)).symm q := by
    rw [LinearEquiv.symm_apply_eq, 𝓛.stabilizerLayerEquiv_mul_apply t _ (index_eq 𝓛 t ht i) hij,
      LinearEquiv.apply_symm_apply]
  rw [hsymm, 𝓛.stabilizerLayerEquiv_mul_apply t _ (index_eq 𝓛 t ht i) hij]

include hg in
/-- The extended family commutes with a translation `z` of shift zero commuting with `t`,
provided its members at `0 ≤ r < g` commute with the action of `z`. -/
theorem extendFamily_commutes_of_commute (c : ∀ r : ℤ, Module.End O (𝓛.Layer r))
    (z : 𝓛.stabilizer) (hz : 𝓛.stabilizerValuation z = 0) (hzt : Commute z t)
    (hc : ∀ r : ℤ, 0 ≤ r → r < g → ∀ (h : r = r + 𝓛.stabilizerValuation z) (q : 𝓛.Layer r),
      𝓛.stabilizerLayerEquiv z r r h (c r q) = c r (𝓛.stabilizerLayerEquiv z r r h q)) :
    𝓛.LayerFamilyCommutes (extendFamily 𝓛 t ht c) z := by
  intro i₀ i hij q
  have hji : i = i₀ := by rw [hij, hz, add_zero]
  subst hji
  set r := i % (g : ℤ)
  set T := t ^ (i / (g : ℤ))
  have hr₀ : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hg.ne')
  have hr : r < g := Int.emod_lt_of_pos _ (by exact_mod_cast hg)
  have hiT : i = r + 𝓛.stabilizerValuation T := index_eq 𝓛 t ht i
  have hrz : r = r + 𝓛.stabilizerValuation z := by rw [hz, add_zero]
  have hcomm : z * T = T * z := (hzt.zpow_right _).eq
  have hzT : i = r + 𝓛.stabilizerValuation (z * T) := by
    rw [𝓛.stabilizerValuation_mul, hz, zero_add]
    exact hiT
  -- the layer action of `z` at `i` is the transport of its action at `r`
  have hTz : i = r + 𝓛.stabilizerValuation (T * z) := by
    rw [𝓛.stabilizerValuation_mul, hz, add_zero]
    exact hiT
  have key (w : 𝓛.Layer r) :
      𝓛.stabilizerLayerEquiv z i i hij (𝓛.stabilizerLayerEquiv T r i hiT w) =
        𝓛.stabilizerLayerEquiv T r i hiT (𝓛.stabilizerLayerEquiv z r r hrz w) := by
    rw [← 𝓛.stabilizerLayerEquiv_mul_apply z T hiT hij hzT,
      stabilizerLayerEquiv_congr 𝓛 hcomm hzT hTz, 𝓛.stabilizerLayerEquiv_mul_apply T z hrz hiT]
  simp only [extendFamily, conjLayer, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  change 𝓛.stabilizerLayerEquiv z i i hij (𝓛.stabilizerLayerEquiv T r i hiT
      (c r ((𝓛.stabilizerLayerEquiv T r i hiT).symm q))) =
    𝓛.stabilizerLayerEquiv T r i hiT
      (c r ((𝓛.stabilizerLayerEquiv T r i hiT).symm (𝓛.stabilizerLayerEquiv z i i hij q)))
  obtain ⟨w, rfl⟩ := (𝓛.stabilizerLayerEquiv T r i hiT).surjective q
  rw [key, LinearEquiv.symm_apply_apply, key, LinearEquiv.symm_apply_apply, hc r hr₀ hr hrz]

include hg ht in
/-- A family commuting with `t` vanishes if it vanishes on `0 ≤ r < g`. -/
theorem eq_zero_of_commutes (D : ∀ i : ℤ, Module.End O (𝓛.Layer i))
    (hD : 𝓛.LayerFamilyCommutes D t) (h0 : ∀ r : ℤ, 0 ≤ r → r < g → D r = 0) (i : ℤ) :
    D i = 0 := by
  have hT : t ^ (i / (g : ℤ)) ∈ 𝓛.layerCommutingSubgroup D :=
    zpow_mem (show t ∈ 𝓛.layerCommutingSubgroup D from hD) _
  have hr₀ : 0 ≤ i % (g : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hg.ne')
  have hr : i % (g : ℤ) < g := Int.emod_lt_of_pos _ (by exact_mod_cast hg)
  refine LinearMap.ext fun q => ?_
  obtain ⟨w, rfl⟩ := (𝓛.stabilizerLayerEquiv _ _ i (index_eq 𝓛 t ht i)).surjective q
  rw [← hT _ i (index_eq 𝓛 t ht i) w, h0 _ hr₀ hr]
  simp

end Extend

end Langlands.BushnellKutzko.NonsplitSimple
