import Langlands.BushnellKutzko.SimpleCharacterTransferDeterminant
import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.SubfieldOrderProof

/-! # Filtered determinant images in the relative endomorphism algebra -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

namespace LatticeChain

variable (L : LatticeChain 𝒪[F] F V)
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)

/-- The spectral relative chain has the normalized period of the base chain. -/
theorem relativeLatticeChain_period_eq_div :
    letI := LocalField.FiniteExtension.normedField F E
    letI := LocalField.FiniteExtension.valuativeRel F E
    letI := LocalField.FiniteExtension.isLocalField F E
    (L.relativeLatticeChain hE (isIntegral_iff_mem_spectralInteger F E)).period =
      L.period / subfieldRamificationIndex F E := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  let C := L.relativeLatticeChain hE (isIntegral_iff_mem_spectralInteger F E)
  let D := L.subfieldChain E hE
  let e : subfieldIntegers F E ≃+* 𝒪[E] :=
    { toFun := fun x => ⟨x, (isIntegral_iff_mem_spectralInteger F E x).mp x.2⟩
      invFun := fun x => ⟨x, (isIntegral_iff_mem_spectralInteger F E x).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hπ' : Irreducible (e.symm π) := hπ.map e.symm
  have hC (v : V) : (π : E) • v ∈ L.lattice (0 + C.period) ↔ v ∈ L.lattice 0 := by
    change (π : E) • v ∈ C.lattice (0 + C.period) ↔ v ∈ C.lattice 0
    rw [C.uniformizer_smul_mem_iff hπ, add_sub_cancel_right]
  have hD (v : V) : (π : E) • v ∈ L.lattice (0 + D.period) ↔ v ∈ L.lattice 0 := by
    have h := D.mem_lattice_stabilizer_iff (D.uniformizerStabilizer hπ') 0 v
    rw [D.uniformizerStabilizer_shift hπ'] at h
    exact h
  have hπ0 := coe_uniformizer_ne_zero hπ
  have hCD : C.period = D.period := by
    have h : L.lattice (0 + C.period) = L.lattice (0 + D.period) := by
      ext v
      have hv := (hC ((π : E)⁻¹ • v)).trans (hD ((π : E)⁻¹ • v)).symm
      simpa only [smul_smul, mul_inv_cancel₀ hπ0, one_smul] using hv
    exact_mod_cast add_left_cancel (L.injective h)
  have hmul := L.fieldShift_uniformizer_mul_ramification E hE hπ'
  change (L.fieldShift E hE (subfieldIntegerUnit E hπ'.ne_zero)).toAdd *
    (subfieldRamificationIndex F E : ℤ) = (L.period : ℤ) at hmul
  rw [← L.subfieldChain_period_eq_shift E hE hπ'] at hmul
  change (D.period : ℤ) * _ = _ at hmul
  rw [← hCD] at hmul
  have hmul' : C.period * subfieldRamificationIndex F E = L.period := by exact_mod_cast hmul
  have hpos : 0 < subfieldRamificationIndex F E := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hmul'
    exact L.period_pos.ne' hmul'.symm
  change C.period = L.period / subfieldRamificationIndex F E
  rw [← hmul', Nat.mul_div_cancel _ hpos]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
/-- Two relative chains with the same lattice subsets give the same filtered units
under restriction of scalars. -/
theorem mem_unitFiltration_restrictScalars_iff {O : Type*} [CommRing O] [Algebra O E]
    [Module O V] [IsScalarTower O E V] (C : LatticeChain O E V)
    (hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ L.lattice i)
    (m : ℕ) (x : (Module.End E V)ˣ) :
    relativeEndUnits E x ∈ L.unitFiltration m ↔ x ∈ C.unitFiltration m := by
  rw [L.mem_unitFiltration, C.mem_unitFiltration, L.mem_order, L.mem_order, C.mem_order,
    C.mem_order, L.mem_endFiltration, C.mem_endFiltration, ← map_inv]
  simp only [← hC]
  rfl

end LatticeChain

/-- The common determinant image of the two filtered groups pulled back to the
relative endomorphism algebra, at equal normalized level. -/
theorem relativeDet_image_inf_unitFiltration (L M : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (hM : ∀ a : Eˣ, subfieldUnits F E V a ∈ M.stabilizer)
    (m₁ m₂ : ℕ)
    (hm : m₁ / (L.period / subfieldRamificationIndex F E) =
      m₂ / (M.period / subfieldRamificationIndex F E)) :
    letI := LocalField.FiniteExtension.normedField F E
    letI := LocalField.FiniteExtension.valuativeRel F E
    letI := LocalField.FiniteExtension.isLocalField F E
    (fun g : (Module.End E V)ˣ => LinearMap.det (g : Module.End E V)) ''
      (((L.unitFiltration (m₁ + 1) ⊓ M.unitFiltration (m₂ + 1)).comap
        (relativeEndUnits E) : Subgroup (Module.End E V)ˣ) : Set (Module.End E V)ˣ) =
      {u | ∃ a : 𝒪[E], a ∈ 𝓂[E] ^ (m₁ / (L.period / subfieldRamificationIndex F E) + 1) ∧
        u = 1 + (a : E)} := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let hInt := isIntegral_iff_mem_spectralInteger F E
  let C := L.relativeLatticeChain hL hInt
  let D := M.relativeLatticeChain hM hInt
  have hC : C.period = L.period / subfieldRamificationIndex F E :=
    L.relativeLatticeChain_period_eq_div hL
  have hD : D.period = M.period / subfieldRamificationIndex F E :=
    M.relativeLatticeChain_period_eq_div hM
  have hEq : (L.unitFiltration (m₁ + 1) ⊓ M.unitFiltration (m₂ + 1)).comap
      (relativeEndUnits E) = C.unitFiltration (m₁ + 1) ⊓ D.unitFiltration (m₂ + 1) := by
    ext g
    exact and_congr
      (L.mem_unitFiltration_restrictScalars_iff C (L.mem_relativeLatticeChain hL hInt) _ g)
      (M.mem_unitFiltration_restrictScalars_iff D (M.mem_relativeLatticeChain hM hInt) _ g)
  rw [hEq, C.det_image_inf_unitFiltration D m₁ m₂ (by rwa [hC, hD]), hC]

/-- A relative unit on the second chain has the same determinant as a relative
unit in both filtered groups when the normalized depths agree. -/
theorem exists_relative_unit_in_inf_with_det (L M : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (hM : ∀ a : Eˣ, subfieldUnits F E V a ∈ M.stabilizer)
    (m₁ m₂ : ℕ)
    (hm : m₁ / (L.period / subfieldRamificationIndex F E) =
      m₂ / (M.period / subfieldRamificationIndex F E))
    {g : (Module.End E V)ˣ} (hg : relativeEndUnits E g ∈ M.unitFiltration (m₂ + 1)) :
    ∃ x : (Module.End E V)ˣ, relativeEndUnits E x ∈ L.unitFiltration (m₁ + 1) ⊓
      M.unitFiltration (m₂ + 1) ∧
      LinearMap.det (x : Module.End E V) = LinearMap.det (g : Module.End E V) := by
  have hImage := relativeDet_image_inf_unitFiltration L M hL hM m₁ m₂ hm
  have hOne := relativeDet_image_inf_unitFiltration M M hM hM m₂ m₂ rfl
  have hd : LinearMap.det (g : Module.End E V) ∈
      (fun x : (Module.End E V)ˣ => LinearMap.det (x : Module.End E V)) ''
      (((M.unitFiltration (m₂ + 1) ⊓ M.unitFiltration (m₂ + 1)).comap
        (relativeEndUnits E) : Subgroup (Module.End E V)ˣ) : Set (Module.End E V)ˣ) :=
    ⟨g, ⟨hg, hg⟩, rfl⟩
  rw [hOne, ← hm, ← hImage] at hd
  exact hd

end Langlands.BushnellKutzko
