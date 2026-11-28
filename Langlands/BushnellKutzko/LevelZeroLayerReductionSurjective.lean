import Langlands.BushnellKutzko.LatticeChainLayerIntertwining
import Langlands.BushnellKutzko.LevelZeroSplitType

/-! # Surjectivity of the layer reduction of `U(𝔄)`

Let `𝓛 = (L_j)` be an `𝔬`-lattice chain of period `e` over a discrete valuation ring `𝔬` with
fraction field `K`, and `𝔄` its hereditary order. The layer reduction
`U(𝔄) → ∏_{0 ≤ i < e} GL(L_i / L_{i+1})` (`LatticeChain.layerReduction`, in chosen bases of
the layers over the residue field) is surjective (`LatticeChain.layerReduction_surjective`),
and its kernel is `U^1(𝔄)` (`LatticeChain.layerReduction_eq_one_of_mem`,
`LatticeChain.mem_unitFiltration_one_of_layerReduction_eq_one`). The lemmas
`LatticeChain.equivFun_layerReduction` and `LatticeChain.layerReduction_apply_entry` describe
the reduction in the coordinates given by the bases.

These are the two halves of the identification `U(𝔄) / U^1(𝔄) ≅ ∏_i GL(L_i / L_{i+1})` used in
Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987),
proof of Theorem 2′(i), printed p. 197, with `𝔄` in the block matrix form (1.9), and in the
proof of Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(8.1.5), printed p. 267: surjectivity together with the equality of the kernel with
`U^1(𝔄)`.

A family of automorphisms of the layers `L_i / L_{i+1}`, `0 ≤ i < e`, is extended to all
`i ∈ ℤ` by transport along the uniformizer, which carries `L_i` onto `L_{i+e}`; the extended
family commutes with the uniformizer and lifts to an element of `𝔄`
(`LatticeChain.exists_order_lift_layers`). Lifting the inverse family as well shows that the
lift is a unit of `𝔄` (`LatticeChain.exists_unitFiltration_layerAction`).
-/

noncomputable section

open IsLocalRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- **Lifting a periodic family of layer automorphisms to a unit.** A family of automorphisms
`Φ_i` of the layers `L_i / L_{i+1}` which commutes with the uniformizer is the layer action of
an element of `𝔄` which is a unit of `𝔄`. -/
theorem exists_unitFiltration_layerAction {π : O} (hπ : Irreducible π)
    (Φ : ∀ i : ℤ, 𝓛.Layer i ≃ₗ[O] 𝓛.Layer i)
    (hΦ : ∀ (i j : ℤ) (h : j = i + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ))
      (q : 𝓛.Layer i), 𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h (Φ i q) =
        Φ j (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h q)) :
    ∃ x : 𝓛.order, ∃ u ∈ 𝓛.unitFiltration 0, (u : Module.End K V) = x.val ∧
      ∀ i : ℤ, 𝓛.layerAction x i = (Φ i).toLinearMap := by
  let D : ∀ i : ℤ, Module.End O (𝓛.Layer i) := fun i => (Φ i).toLinearMap
  let D' : ∀ i : ℤ, Module.End O (𝓛.Layer i) := fun i => (Φ i).symm.toLinearMap
  have hD : 𝓛.LayerFamilyCommutes D (𝓛.uniformizerStabilizer hπ) := fun i j h q => hΦ i j h q
  have hD' : 𝓛.LayerFamilyCommutes D' (𝓛.uniformizerStabilizer hπ) := by
    intro i j h q
    change 𝓛.stabilizerLayerEquiv _ i j h ((Φ i).symm q) =
      (Φ j).symm (𝓛.stabilizerLayerEquiv _ i j h q)
    rw [LinearEquiv.eq_symm_apply, ← hΦ i j h, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := 𝓛.exists_order_lift_layers hπ D hD
  obtain ⟨x', hx'⟩ := 𝓛.exists_order_lift_layers hπ D' hD'
  have hxx' : x.val * x'.val - 1 ∈ 𝓛.endFiltration 1 := by
    have h := (𝓛.layerAction_eq_iff (x * x') 1).mp (fun i => by
      rw [layerAction_mul, hx, hx', layerAction_one]
      apply LinearMap.ext
      intro q
      exact (Φ i).apply_symm_apply q)
    simpa using h
  have hx'x : x'.val * x.val - 1 ∈ 𝓛.endFiltration 1 := by
    have h := (𝓛.layerAction_eq_iff (x' * x) 1).mp (fun i => by
      rw [layerAction_mul, hx, hx', layerAction_one]
      apply LinearMap.ext
      intro q
      exact (Φ i).symm_apply_apply q)
    simpa using h
  obtain ⟨h₁, hh₁, hh₁v⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl hxx'
  obtain ⟨h₂, hh₂, hh₂v⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl hx'x
  have hh₁v' : (h₁ : Module.End K V) = x.val * x'.val := by rw [hh₁v]; abel
  have hh₂v' : (h₂ : Module.End K V) = x'.val * x.val := by rw [hh₂v]; abel
  set y : Module.End K V := x'.val * ((h₁⁻¹ : (Module.End K V)ˣ) : Module.End K V) with hy
  have hr : x.val * y = 1 := by
    rw [hy, ← mul_assoc, ← hh₁v', Units.mul_inv]
  have hl' : ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * x.val = 1 := by
    rw [mul_assoc, ← hh₂v', Units.inv_mul]
  have hyeq : y = ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val := by
    calc y = (((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * x.val) * y := by
          rw [hl', one_mul]
      _ = ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * (x.val * y) := by
          simp only [mul_assoc]
      _ = _ := by rw [hr, mul_one]
  have hl : y * x.val = 1 := by rw [hyeq, hl']
  let u : (Module.End K V)ˣ := ⟨x.val, y, hr, hl⟩
  have hyO : y ∈ 𝓛.order := mul_mem x'.prop hh₁.2.1
  exact ⟨x, u, (𝓛.mem_unitFiltration_zero).mpr ⟨x.prop, hyO⟩, rfl, hx⟩

section Periodic

variable {π : O} (hπ : Irreducible π) {d : Fin 𝓛.period → ℕ}
  (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
  (A : ∀ i, GeneralLinear (d i) (ResidueField O))

/-- The automorphism of the layer `L_s / L_{s+1}`, `0 ≤ s < e`, with matrix `A s` in the
basis `b s`. -/
private def layerMatrixEquiv (s : Fin 𝓛.period) : 𝓛.Layer (s : ℕ) ≃ₗ[O] 𝓛.Layer (s : ℕ) :=
  ((Matrix.GeneralLinearGroup.toLin' (b s) (A s)).toLinearEquiv).restrictScalars O

/-- The transport of `layerMatrixEquiv b A s` to the layer `L_j / L_{j+1}`, `j = s + e k`, along
the `k`-th power of the uniformizer. -/
private def periodicLayerEquiv (s : Fin 𝓛.period) (k j : ℤ)
    (hj : j = ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ k)) :
    𝓛.Layer j ≃ₗ[O] 𝓛.Layer j :=
  (𝓛.stabilizerLayerEquiv _ _ j hj).symm.trans
    ((𝓛.layerMatrixEquiv b A s).trans (𝓛.stabilizerLayerEquiv _ _ j hj))

/-- The residue of `j` modulo the period, as an element of `Fin e`. -/
private def periodRem (j : ℤ) : Fin 𝓛.period :=
  ⟨(j % (𝓛.period : ℤ)).toNat, by
    have hpos : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have h₁ := Int.emod_nonneg j hpos.ne'
    have h₂ := Int.emod_lt_of_pos j hpos
    omega⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
private theorem periodRem_coe (j : ℤ) :
    (((𝓛.periodRem j : ℕ)) : ℤ) = j % (𝓛.period : ℤ) := by
  have hpos : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have h₁ := Int.emod_nonneg j hpos.ne'
  simp only [periodRem]
  omega

private theorem stabilizerValuation_uniformizer_zpow (k : ℤ) :
    𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ k) = k * 𝓛.period := by
  rw [stabilizerValuation_zpow, uniformizerStabilizer_shift]

private theorem periodRem_eq (j : ℤ) :
    j = ((𝓛.periodRem j : ℕ) : ℤ) +
      𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ (j / (𝓛.period : ℤ))) := by
  rw [stabilizerValuation_uniformizer_zpow, periodRem_coe]
  linear_combination (Int.emod_add_mul_ediv j (𝓛.period : ℤ)).symm

/-- The periodic extension of the family `layerMatrixEquiv b A`. -/
private def periodicFamily (j : ℤ) : 𝓛.Layer j ≃ₗ[O] 𝓛.Layer j :=
  𝓛.periodicLayerEquiv hπ b A (𝓛.periodRem j) (j / (𝓛.period : ℤ)) j (𝓛.periodRem_eq hπ j)

private theorem periodicLayerEquiv_eq (s : Fin 𝓛.period) (k j : ℤ)
    (hj : j = ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ k)) :
    𝓛.periodicLayerEquiv hπ b A s k j hj = 𝓛.periodicFamily hπ b A j := by
  have hpos : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hs₀ := s.isLt
  have hj' : ((s : ℕ) : ℤ) + (𝓛.period : ℤ) * k = j := by
    rw [hj, stabilizerValuation_uniformizer_zpow]
    ring
  obtain ⟨hk, hs⟩ := (Int.ediv_emod_unique hpos).mpr ⟨hj', by omega, by omega⟩
  have hs' : 𝓛.periodRem j = s := Fin.ext (by
    have := 𝓛.periodRem_coe j
    omega)
  subst hk
  subst hs'
  rfl

private theorem periodicFamily_base (s : Fin 𝓛.period) (q : 𝓛.Layer (s : ℕ)) :
    𝓛.periodicFamily hπ b A (s : ℕ) q = 𝓛.layerMatrixEquiv b A s q := by
  have h0 : (((s : ℕ) : ℤ)) =
      ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ (0 : ℤ)) := by
    rw [stabilizerValuation_uniformizer_zpow]
    ring
  have h1 : ((s : ℕ) : ℤ) = ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation 1 := by simp
  have hid : ∀ r : 𝓛.Layer (s : ℕ), 𝓛.stabilizerLayerEquiv _ _ _ h0 r = r := fun r => by
    rw [𝓛.stabilizerLayerEquiv_congr (zpow_zero _) h0 h1, stabilizerLayerEquiv_one_apply]
  rw [← 𝓛.periodicLayerEquiv_eq hπ b A s 0 _ h0]
  have hsymm : (𝓛.stabilizerLayerEquiv _ _ _ h0).symm q = q := by
    rw [LinearEquiv.symm_apply_eq, hid]
  simp only [periodicLayerEquiv, LinearEquiv.trans_apply, hsymm, hid]

private theorem periodicLayerEquiv_commutes (s : Fin 𝓛.period) (k i j : ℤ)
    (hi : i = ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ k))
    (hj : j = ((s : ℕ) : ℤ) + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ (k + 1)))
    (h : j = i + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ)) (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h
        (𝓛.periodicLayerEquiv hπ b A s k i hi q) =
      𝓛.periodicLayerEquiv hπ b A s (k + 1) j hj
        (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h q) := by
  have hx : 𝓛.uniformizerStabilizer hπ ^ (k + 1) =
      𝓛.uniformizerStabilizer hπ * 𝓛.uniformizerStabilizer hπ ^ k := by
    rw [add_comm, zpow_one_add]
  have hgh : j = ((s : ℕ) : ℤ) +
      𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ * 𝓛.uniformizerStabilizer hπ ^ k) :=
    hx ▸ hj
  have key : ∀ r : 𝓛.Layer (s : ℕ),
      𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ ^ (k + 1)) _ j hj r =
        𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h
          (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ ^ k) _ i hi r) := fun r => by
    rw [𝓛.stabilizerLayerEquiv_congr hx hj hgh,
      𝓛.stabilizerLayerEquiv_mul_apply _ _ hi h hgh]
  have hsymm : (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ ^ (k + 1)) _ j hj).symm
      (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h q) =
      (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ ^ k) _ i hi).symm q := by
    rw [LinearEquiv.symm_apply_eq, key, LinearEquiv.apply_symm_apply]
  simp only [periodicLayerEquiv, LinearEquiv.trans_apply, hsymm, key]

private theorem periodicFamily_commutes (i j : ℤ)
    (h : j = i + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ)) (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h
        (𝓛.periodicFamily hπ b A i q) =
      𝓛.periodicFamily hπ b A j (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h q) := by
  have hi := 𝓛.periodRem_eq hπ i
  have hj : j = ((𝓛.periodRem i : ℕ) : ℤ) +
      𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ ^ (i / (𝓛.period : ℤ) + 1)) := by
    have hi' := hi
    rw [stabilizerValuation_uniformizer_zpow] at hi'
    rw [stabilizerValuation_uniformizer_zpow, h, uniformizerStabilizer_shift]
    linear_combination hi'
  rw [← 𝓛.periodicLayerEquiv_eq hπ b A _ _ j hj]
  exact 𝓛.periodicLayerEquiv_commutes hπ b A _ _ i j hi hj h q

end Periodic

/-- **Every layer is a translate of a layer of one period**: for each `j`, the layer
`L_j / L_{j+1}` is isomorphic to `L_s / L_{s+1}` for some `0 ≤ s < e`, by a power of a
uniformizer. -/
theorem exists_layer_linearEquiv (j : ℤ) :
    ∃ s : Fin 𝓛.period, Nonempty (𝓛.Layer (s : ℕ) ≃ₗ[O] 𝓛.Layer j) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact ⟨𝓛.periodRem j, ⟨𝓛.stabilizerLayerEquiv _ _ j (𝓛.periodRem_eq hπ j)⟩⟩

/-- **The layer reduction of `U(𝔄)` is surjective**: every family of invertible matrices over
the residue field, one for each layer `L_i / L_{i+1}` with `0 ≤ i < e`, is the family of
matrices of some `u ∈ U(𝔄)` acting on the layers. -/
theorem layerReduction_surjective {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ))) :
    Function.Surjective (𝓛.layerReduction b) := by
  intro A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x, u, hu, hux, hx⟩ := 𝓛.exists_unitFiltration_layerAction hπ
    (𝓛.periodicFamily hπ b A) (𝓛.periodicFamily_commutes hπ b A)
  refine ⟨⟨u, hu⟩, funext fun i => ?_⟩
  apply (Matrix.GeneralLinearGroup.toLin' (b i)).injective
  apply Units.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective _ _ q
  have h₁ := 𝓛.layerReduction_spec b ⟨u, hu⟩ i v hv
  have h₂ := LinearMap.congr_fun (hx (i : ℕ)) (𝓛.intervalMk _ _ v hv)
  rw [layerAction_mk] at h₂
  change (Matrix.GeneralLinearGroup.toLin' (b i) (𝓛.layerReduction b ⟨u, hu⟩ i)).toLinearEquiv
      (𝓛.intervalMk _ _ v hv) =
    (Matrix.GeneralLinearGroup.toLin' (b i) (A i)).toLinearEquiv (𝓛.intervalMk _ _ v hv)
  rw [h₁]
  change _ = 𝓛.layerMatrixEquiv b A i (𝓛.intervalMk _ _ v hv)
  rw [← 𝓛.periodicFamily_base hπ b A i]
  refine Eq.trans ?_ h₂
  simp only [hux]

omit [IsFractionRing O K] in
/-- **The layer reduction in coordinates**: the coordinates of `u v` in the basis `b i` of
`L_i / L_{i+1}` are the image of the coordinates of `v` under the `i`-th matrix of
`layerReduction b u`. -/
theorem equivFun_layerReduction {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
    (g : 𝓛.unitFiltration 0) (i : Fin 𝓛.period) (v : V) (hv : v ∈ 𝓛.lattice (i : ℕ)) :
    (b i).equivFun (𝓛.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) ((g.1 : Module.End K V) v)
      (𝓛.mem_order.mp g.2.1 _ _ hv)) =
    Matrix.mulVec ((𝓛.layerReduction b g i : GeneralLinear (d i) (ResidueField O)) :
        Matrix (Fin (d i)) (Fin (d i)) (ResidueField O))
      ((b i).equivFun (𝓛.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) v hv)) := by
  rw [← 𝓛.layerReduction_spec b g i v hv, Matrix.GeneralLinearGroup.toLin'_apply,
    Fintype.linearCombination_apply, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

omit [IsFractionRing O K] in
/-- **The entries of the layer reduction**: if `v ∈ L_i` represents the basis vector `b_i(y)`,
the `(x, y)` entry of the `i`-th matrix of `layerReduction b u` is the `x`-th coordinate of the
class of `u v`. -/
theorem layerReduction_apply_entry {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
    (g : 𝓛.unitFiltration 0) (i : Fin 𝓛.period) (x y : Fin (d i)) (v : V)
    (hv : v ∈ 𝓛.lattice (i : ℕ)) (hy : 𝓛.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) v hv = b i y) :
    ((𝓛.layerReduction b g i : GeneralLinear (d i) (ResidueField O)) :
        Matrix (Fin (d i)) (Fin (d i)) (ResidueField O)) x y =
      (b i).repr (𝓛.intervalMk (i : ℕ) ((i : ℕ) + 1 : ℤ) ((g.1 : Module.End K V) v)
        (𝓛.mem_order.mp g.2.1 _ _ hv)) x := by
  classical
  have h := congrFun (𝓛.equivFun_layerReduction b g i v hv) x
  have hs : (b i).equivFun (b i y) = Pi.single y 1 := by
    ext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [hy, hs, Matrix.mulVec_single_one, Module.Basis.equivFun_apply] at h
  exact h.symm

omit [IsFractionRing O K] in
/-- An element of `U(𝔄)` acting trivially on one layer `L_i / L_{i+1}` has trivial `i`-th
component under the layer reduction. -/
theorem layerReduction_apply_eq_one {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
    (g : 𝓛.unitFiltration 0) (i : Fin 𝓛.period)
    (hg : ∀ v ∈ 𝓛.lattice (i : ℕ), (g.1 : Module.End K V) v - v ∈ 𝓛.lattice ((i : ℕ) + 1)) :
    𝓛.layerReduction b g i = 1 := by
  apply (Matrix.GeneralLinearGroup.toLin' (b i)).injective
  apply Units.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective _ _ q
  have h₁ := 𝓛.layerReduction_spec b g i v hv
  change (Matrix.GeneralLinearGroup.toLin' (b i) (𝓛.layerReduction b g i)).toLinearEquiv
      (𝓛.intervalMk _ _ v hv) = _
  rw [h₁, map_one]
  change _ = 𝓛.intervalMk _ _ v hv
  rw [intervalMk_eq_iff]
  exact hg v hv

omit [IsFractionRing O K] in
/-- **`U^1(𝔄)` lies in the kernel of the layer reduction.** -/
theorem layerReduction_eq_one_of_mem {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
    (g : 𝓛.unitFiltration 0) (hg : (g : (Module.End K V)ˣ) ∈ 𝓛.unitFiltration 1) :
    𝓛.layerReduction b g = 1 := by
  funext i
  refine 𝓛.layerReduction_apply_eq_one b g i fun v hv => ?_
  have h := hg.2.2 _ v hv
  simpa using h

/-- **The kernel of the layer reduction is `U^1(𝔄)`**: an element of `U(𝔄)` acting trivially on
the layers `L_i / L_{i+1}`, `0 ≤ i < e`, lies in `U^1(𝔄)`. -/
theorem mem_unitFiltration_one_of_layerReduction_eq_one {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField O) (𝓛.Layer (i : ℕ)))
    (g : 𝓛.unitFiltration 0) (hg : 𝓛.layerReduction b g = 1) :
    (g : (Module.End K V)ˣ) ∈ 𝓛.unitFiltration 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hg0 := 𝓛.mem_unitFiltration_zero.mp g.2
  let x : 𝓛.order := ⟨((g : (Module.End K V)ˣ) : Module.End K V), hg0.1⟩
  have hbase : ∀ s : Fin 𝓛.period, 𝓛.layerAction x ((s : ℕ) : ℤ) = LinearMap.id := by
    intro s
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective _ _ q
    have h₁ := 𝓛.layerReduction_spec b g s v hv
    rw [hg, Pi.one_apply, map_one] at h₁
    rw [layerAction_mk]
    exact h₁.symm
  have hstep : ∀ i : ℤ, 𝓛.layerAction x i = LinearMap.id ↔
      𝓛.layerAction x (i + 𝓛.period) = LinearMap.id := by
    intro i
    have hj : i + (𝓛.period : ℤ) = i + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ) := by
      rw [uniformizerStabilizer_shift]
    have hc := 𝓛.layerAction_commutes_uniformizer hπ x i (i + 𝓛.period) hj
    constructor
    · intro h
      apply LinearMap.ext
      intro q
      obtain ⟨r, rfl⟩ := (𝓛.stabilizerLayerEquiv _ i _ hj).surjective q
      rw [← hc r, h]
      rfl
    · intro h
      apply LinearMap.ext
      intro q
      apply (𝓛.stabilizerLayerEquiv _ i _ hj).injective
      rw [hc q, h]
      rfl
  have hall : ∀ i : ℤ, 𝓛.layerAction x i = LinearMap.id := by
    intro i
    have key : ∀ k : ℤ,
        𝓛.layerAction x (i % (𝓛.period : ℤ) + 𝓛.period * k) = LinearMap.id := by
      intro k
      induction k using Int.induction_on with
      | zero =>
        have h := hbase (𝓛.periodRem i)
        rw [periodRem_coe] at h
        rw [mul_zero, add_zero]
        exact h
      | succ k ih =>
        have h := (hstep _).1 ih
        rwa [show i % (𝓛.period : ℤ) + 𝓛.period * k + 𝓛.period =
          i % (𝓛.period : ℤ) + 𝓛.period * (k + 1) by ring] at h
      | pred k ih =>
        apply (hstep _).2
        rwa [show i % (𝓛.period : ℤ) + 𝓛.period * (-(k : ℤ) - 1) + 𝓛.period =
          i % (𝓛.period : ℤ) + 𝓛.period * (-(k : ℤ)) by ring]
    have h := key (i / (𝓛.period : ℤ))
    rwa [Int.emod_add_mul_ediv] at h
  have h := (𝓛.layerAction_eq_iff x 1).mp (fun i => by rw [hall i, layerAction_one])
  exact 𝓛.mem_unitFiltration.mpr ⟨hg0.1, hg0.2, by simpa using h⟩

end Langlands.BushnellKutzko.LatticeChain
