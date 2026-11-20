import Langlands.BushnellKutzko.StratumEquivalenceResidue
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # The residue degree from `𝔅 + 𝔓` (BK93 (2.1.4)(iii))

Helper results for `StratumEquivalenceStatement`. For an `𝔬_F`-submodule `M` of `End_F(V)` let
`Z(M) = {x ∈ 𝔄 : (x m - m x) L_0 ⊆ L_1 for all m ∈ M}` and let `K = {x : x L_0 ⊆ L_1}`.
When `E` is a finite field extension of `F` whose units normalize `𝓛` and
`M = 𝔅_E + 𝔓`, the action of `𝔬_E` on `V` induces an `𝔬_F`-linear isomorphism
`𝔬_E/𝔭_E ≅ Z(M)/(Z(M) ∩ K)`. Hence the residue degree of `E` depends only on `𝓛` and `M`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV uE uE'

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

theorem apply_mem_of_mem_endFiltration_zero {x : Module.End F V} (hx : x ∈ P 0) {i : ℤ}
    {v : V} (hv : v ∈ L i) : x v ∈ L i := by
  have h := hx i v hv
  rwa [add_zero] at h

/-- `Z(M) = {x ∈ 𝔄 : (x m - m x) L_0 ⊆ L_1 for all m ∈ M}`. -/
def residueCommutant (M : Submodule 𝒪[F] (Module.End F V)) :
    Submodule 𝒪[F] (Module.End F V) where
  carrier := {x | x ∈ P 0 ∧ ∀ m ∈ M, ∀ v ∈ L 0, (x * m - m * x) v ∈ L 1}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨add_mem hx0 hy0, fun m hm v hv => ?_⟩
    have h : ((x + y) * m - m * (x + y)) v = (x * m - m * x) v + (y * m - m * y) v := by
      simp only [add_mul, mul_add, LinearMap.sub_apply, LinearMap.add_apply]
      abel
    rw [h]
    exact add_mem (hx m hm v hv) (hy m hm v hv)
  zero_mem' := ⟨zero_mem _, fun m _ v _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx0, hx⟩
    refine ⟨Submodule.smul_mem _ c hx0, fun m hm v hv => ?_⟩
    have hc : ∀ w : V, c • w = (c : F) • w := fun _ => rfl
    have h : ((c • x) * m - m * (c • x)) v = c • ((x * m - m * x) v) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hc, map_smul,
        smul_sub]
    rw [h]
    exact Submodule.smul_mem _ c (hx m hm v hv)

/-- `K = {x : x L_0 ⊆ L_1}`. -/
def layerKernel : Submodule 𝒪[F] (Module.End F V) where
  carrier := {x | ∀ v ∈ L 0, x v ∈ L 1}
  add_mem' := fun hx hy v hv => add_mem (hx v hv) (hy v hv)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun c _ hx v hv => Submodule.smul_mem _ c (hx v hv)

/-- `Z(M)/(Z(M) ∩ K)`, an `𝔬_F`-module attached to `𝓛` and `M` only. -/
abbrev residueQuotient (M : Submodule 𝒪[F] (Module.End F V)) :=
  residueCommutant 𝓛 M ⧸ (layerKernel 𝓛).comap (residueCommutant 𝓛 M).subtype

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝔬" => subfieldIntegers F E

theorem smul_mem_of_shift_nonneg {a : E} (ha : 0 ≤ shift 𝓛 hE a) {i : ℤ} {v : V}
    (hv : v ∈ L i) : a • v ∈ L i := by
  by_cases h0 : a = 0
  · rw [h0, zero_smul]
    exact zero_mem _
  exact smul_mem_of_shift_le 𝓛 hE h0 (by omega) hv

include hE in
/-- Elements of `𝔬_E` act through `Z(𝔅_E + 𝔓)`. -/
theorem subfieldEmbedding_mem_residueCommutant {a : E} (ha : a ∈ 𝔬) :
    subfieldEmbedding F E V a ∈ residueCommutant 𝓛 (fieldOrder 𝓛 E ⊔ P 1) := by
  have hs := shift_nonneg_of_mem 𝓛 hE ha
  refine ⟨fun i v hv => ?_, fun m hm v hv => ?_⟩
  · rw [add_zero]
    exact smul_mem_of_shift_nonneg 𝓛 hE hs hv
  obtain ⟨b, hb, p, hp, rfl⟩ := Submodule.mem_sup.mp hm
  have hb' : ∀ (c : E) (w : V), b (c • w) = c • b w := hb.2
  change a • (b + p) v - (b + p) (a • v) ∈ L 1
  rw [LinearMap.add_apply, LinearMap.add_apply, hb' a v, smul_add, add_sub_add_left_eq_sub]
  have h1 : p v ∈ L 1 := by simpa using hp 0 v hv
  have h2 : p (a • v) ∈ L 1 := by simpa using hp 0 (a • v) (smul_mem_of_shift_nonneg 𝓛 hE hs hv)
  exact sub_mem (smul_mem_of_shift_nonneg 𝓛 hE hs h1) h2

/-- The action map `𝔬_E → Z(𝔅_E + 𝔓)`. -/
def integerMap : 𝔬 →ₗ[𝒪[F]] residueCommutant 𝓛 (fieldOrder 𝓛 E ⊔ P 1) where
  toFun a := ⟨subfieldEmbedding F E V (a : E), subfieldEmbedding_mem_residueCommutant 𝓛 hE a.2⟩
  map_add' a b := Subtype.ext (map_add (subfieldEmbedding F E V) (a : E) (b : E))
  map_smul' c a := by
    have := isScalarTower_integer (F := F) (E := E) (V := V)
    apply Subtype.ext
    ext v
    change ((c • a : 𝔬) : E) • v = c • ((a : E) • v)
    rw [Subalgebra.coe_smul, smul_assoc]

theorem integerMap_apply (a : 𝔬) (v : V) : (integerMap 𝓛 hE a : Module.End F V) v = (a : E) • v :=
  rfl

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]
  [FiniteDimensional F E]

/-- The kernel of `𝔬_E → Z/(Z ∩ K)` is `𝔭_E`. -/
theorem integerMap_mem_layerKernel_iff (a : 𝔬) :
    (integerMap 𝓛 hE a : Module.End F V) ∈ layerKernel 𝓛 ↔ a ∈ subfieldMaximalIdeal F E := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝔬
  by_cases ha : a = 0
  · subst ha
    refine ⟨fun _ => zero_mem _, fun _ => ?_⟩
    rw [map_zero]
    exact zero_mem (layerKernel 𝓛)
  rw [mem_maximalIdeal_iff 𝓛 hE hϖ ha]
  have ha' : (a : E) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · intro h
    obtain ⟨n, w, k, c, hw, hu⟩ := exists_basis_depth_zero 𝓛 hE
    have h1 := hu.smul 𝓛 hE ha'
    rw [zero_add] at h1
    exact h1.le 𝓛 (h _ hu.1)
  · intro h v hv
    exact smul_mem_of_shift_le 𝓛 hE ha' (by omega) hv

/-- Every element of `Z(𝔅_E + 𝔓)` agrees with an element of `𝔬_E` modulo `K`. -/
theorem exists_integer_sub_mem_layerKernel {x : Module.End F V}
    (hx : x ∈ residueCommutant 𝓛 (fieldOrder 𝓛 E ⊔ P 1)) :
    ∃ a : 𝔬, x - (integerMap 𝓛 hE a : Module.End F V) ∈ layerKernel 𝓛 := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝔬
  obtain ⟨n, w, k, c, hw, hu⟩ := exists_basis_depth_zero 𝓛 hE
  have hc : c ≠ 0 := by
    rintro rfl
    exact hu.ne_zero 𝓛 (zero_smul E _)
  set u := c • w k with hu_def
  set t := w.coord k (x u) with ht_def
  set a := t * c⁻¹ with ha_def
  have hau : a • u = t • w k := by
    rw [hu_def, smul_smul, ha_def, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hxu : x u ∈ L 0 := apply_mem_of_mem_endFiltration_zero 𝓛 hx.1 hu.1
  have ha : a ∈ 𝔬 := by
    by_cases ha0 : a = 0
    · rw [ha0]
      exact zero_mem _
    rw [mem_integers_iff 𝓛 hE hϖ ha0]
    have h1 := hu.smul 𝓛 hE ha0
    rw [zero_add] at h1
    apply h1.le 𝓛
    rw [hau]
    exact coord_smul_mem 𝓛 hw hxu k
  refine ⟨⟨a, ha⟩, ?_⟩
  have hp := rankOne_mem_fieldOrder 𝓛 hE hw hu hu.1
  have h1 : x u - a • u ∈ L 1 := by
    have h := hx.2 _ (Submodule.mem_sup_left hp) u hu.1
    have e1 : (x * rankOne F w k c u - rankOne F w k c u * x) u = x u - a • u := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        rankOne_apply_basis k hc, rankOne_apply, smul_smul]
    rwa [e1] at h
  intro v hv
  have hm := rankOne_mem_fieldOrder 𝓛 hE hw hu hv
  set m := rankOne F w k c v with hm_def
  have hmu : m u = v := rankOne_apply_basis k hc v
  have hmc : ∀ (b : E) (y : V), m (b • y) = b • m y := hm.2
  have hcomm := hx.2 _ (Submodule.mem_sup_left hm) u hu.1
  change x v - a • v ∈ L 1
  have e2 : x v - a • v = (x * m - m * x) u + m (x u - a • u) := by
    conv_lhs => rw [← hmu]
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hmc a u]
    abel
  rw [e2]
  exact add_mem hcomm (apply_mem_of_mem_endFiltration_zero 𝓛 hm.1 h1)

include hE in
/-- `𝔬_E/𝔭_E` and `Z(𝔅_E + 𝔓)/(Z ∩ K)` have the same length over `𝔬_F`. -/
theorem length_residueRing_eq :
    Module.length 𝒪[F] (subfieldResidueRing F E) =
      Module.length 𝒪[F] (residueQuotient 𝓛 (fieldOrder 𝓛 E ⊔ P 1)) := by
  set K' := (layerKernel 𝓛).comap (residueCommutant 𝓛 (fieldOrder 𝓛 E ⊔ P 1)).subtype
    with hK'
  set φ := K'.mkQ ∘ₗ integerMap 𝓛 hE with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := K'.mkQ_surjective q
    obtain ⟨a, ha⟩ := exists_integer_sub_mem_layerKernel 𝓛 hE hx
    refine ⟨a, ?_⟩
    rw [hφ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    change (integerMap 𝓛 hE a : Module.End F V) - x ∈ layerKernel 𝓛
    rw [← neg_sub]
    exact neg_mem ha
  have hker : LinearMap.ker φ = (subfieldMaximalIdeal F E).restrictScalars 𝒪[F] := by
    ext a
    rw [LinearMap.mem_ker, hφ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
    exact integerMap_mem_layerKernel_iff 𝓛 hE a
  have e1 := LinearMap.quotKerEquivOfSurjective φ hsurj
  have e2 := Submodule.Quotient.restrictScalarsEquiv 𝒪[F] (subfieldMaximalIdeal F E)
  exact (e2.symm.trans ((Submodule.quotEquivOfEq _ _ hker.symm).trans e1)).length_eq

include hE in
/-- Two normalizing fields with the same `𝔅 + 𝔓` have the same residue degree. -/
theorem residueDegree_eq_of_sup_eq
    {E' : Type uE'} [Field E'] [Algebra F E'] [Module E' V] [IsScalarTower F E' V]
    [FiniteDimensional F E']
    (hE' : ∀ a : E'ˣ, subfieldUnits F E' V a ∈ 𝓛.stabilizer)
    (hM : fieldOrder 𝓛 E ⊔ P 1 = fieldOrder 𝓛 E' ⊔ P 1) :
    subfieldResidueDegree F E = subfieldResidueDegree F E' := by
  unfold subfieldResidueDegree
  rw [length_residueRing_eq 𝓛 hE, length_residueRing_eq 𝓛 hE', hM]

end LocalField

end StratumEquivalence

end Langlands.BushnellKutzko
