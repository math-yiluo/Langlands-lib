import Langlands.BushnellKutzko.SimpleCharacterTransferRelative
import Langlands.BushnellKutzko.StratumEquivalenceCritical

/-! # Splitting the intersection of two simple-character lattices -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

section Retraction

variable {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  [Module E V] [IsScalarTower F E V]

/-- A normalizing field admits one retraction onto the relative endomorphisms
preserving the filtration of each of two chains. -/
theorem exists_filtration_retraction (L M : LatticeChain 𝒪[F] F V)
    (hL : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (hM : ∀ a : Eˣ, subfieldUnits F E V a ∈ M.stabilizer) :
    ∃ p : A →+ Module.End E V,
      (∀ x : Module.End E V, p (x.restrictScalars F) = x) ∧
      (∀ k x, x ∈ L.endFiltration k → (p x).restrictScalars F ∈ L.endFiltration k) ∧
      (∀ k x, x ∈ M.endFiltration k → (p x).restrictScalars F ∈ M.endFiltration k) := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let hi := isIntegral_iff_mem_spectralInteger F E
  let C := L.relativeLatticeChain hL hi
  let D := M.relativeLatticeChain hM hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨r, b, _, hbC, hbD⟩ := C.exists_common_splitting_basis D hπ
  let p : A →+ Module.End E V :=
    { toFun := fun x => b.constr E (fun j => x (b j))
      map_zero' := (b.constr E).map_zero
      map_add' := fun x y => (b.constr E).map_add (fun j => x (b j)) (fun j => y (b j)) }
  have hpres (N : LatticeChain 𝒪[E] E V) (hN : N.Splits b) (k : ℤ) (x : A)
      (hx : ∀ i v, v ∈ N.lattice i → x v ∈ N.lattice (i + k)) :
      p x ∈ N.endFiltration k := by
    intro i v hv
    change (b.constr E (fun j => x (b j))) v ∈ N.lattice (i + k)
    rw [b.constr_apply_fintype E]
    refine Submodule.sum_mem _ fun j _ => ?_
    let c := b.repr v j
    change c • x (b j) ∈ N.lattice (i + k)
    by_cases hc : c = 0
    · simp [hc]
    have hj : c • b j ∈ N.lattice i := hN (fun j => b.repr v j) i (by rwa [b.sum_repr]) j
    rw [N.smul_mem_iff hπ hc] at hj ⊢
    simpa only [sub_add_eq_add_sub] using hx _ _ hj
  refine ⟨p, ?_, fun k x hx => ?_, fun k x hx => ?_⟩
  · intro x
    exact b.constr_self E x
  · exact hpres C hbC k x hx
  · exact hpres D hbD k x hx

end Retraction

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A map commuting with the generator is linear for the generated algebra. -/
theorem map_smul_elementAlgebra_of_commute {β x : A} (h : Commute β x)
    (a : elementAlgebra β) (v : V) : x (a • v) = a • x v := by
  have hle : elementAlgebra β ≤ Subalgebra.centralizer F {x} := by
    apply Algebra.adjoin_le
    rintro _ rfl
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact h.symm
  have ha := hle a.2
  rw [Subalgebra.mem_centralizer_iff] at ha
  exact LinearMap.congr_fun (ha x rfl) v

/-- The common projection can be taken to fix the adjoint kernel for `β`
and to take values in that kernel. -/
theorem exists_centralizer_filtration_retraction (L M : LatticeChain 𝒪[F] F V)
    (β : A) (hfield : IsField (elementAlgebra β))
    (hL : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer) :
    ∃ p : A →+ A,
      (∀ x, adjointMap 𝒪[F] β (p x) = 0) ∧
      (∀ x, adjointMap 𝒪[F] β x = 0 → p x = x) ∧
      (∀ k x, x ∈ L.endFiltration k → p x ∈ L.endFiltration k) ∧
      (∀ k x, x ∈ M.endFiltration k → p x ∈ M.endFiltration k) := by
  let E := elementAlgebra β
  let : Field E := hfield.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  obtain ⟨p, hfix, hpL, hpM⟩ := exists_filtration_retraction L M hL hM
  let ι : Module.End E V →ₗ[F] A :=
    LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)
  refine ⟨ι.toAddMonoidHom.comp p, ?_, ?_, hpL, hpM⟩
  · intro x
    rw [StratumEquivalence.adjointMap_apply, sub_eq_zero]
    ext v
    let a : E := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
    change a • (p x) v = (p x) (a • v)
    exact ((p x).map_smul a v).symm
  · intro x hx
    have h : Commute β x := by
      rwa [StratumEquivalence.adjointMap_apply, sub_eq_zero] at hx
    let z : Module.End E V :=
      { toFun := x
        map_add' := x.map_add
        map_smul' := map_smul_elementAlgebra_of_commute h }
    exact congrArg (LinearMap.restrictScalars F) (hfix z)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerLattice_le_simpleHLattice (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) : centralizerLattice L β 0 ≤ simpleHLattice L n β tail := by
  cases tail <;> exact le_sup_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleHLattice_le_centralizer_sup (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) :
    let c := simpleHCutoff (if tail.isEmpty then n else finiteCriticalDepth L n β)
    simpleHLattice L n β tail ≤ centralizerLattice L β 0 ⊔ L.endFiltration c := by
  cases tail with
  | nil => exact le_rfl
  | cons γ tail => exact sup_le_sup_left inf_le_right _

/-- At the given depths, the lattice intersection splits into its centralizer part and a
common part at the two upper cutoffs. The same projection is used on both sides. -/
theorem exists_simpleHLayer_inf_decomposition (L M : LatticeChain 𝒪[F] F V)
    (n₁ n₂ : ℤ) (β : A) (tail₁ tail₂ : List A) (k₁ k₂ : ℕ)
    (hfield : IsField (elementAlgebra β))
    (hL : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    {x : A} (hx₁ : x ∈ simpleHLayer L n₁ β tail₁ k₁)
    (hx₂ : x ∈ simpleHLayer M n₂ β tail₂ k₂) :
    let c₁ := simpleHCutoff (if tail₁.isEmpty then n₁ else finiteCriticalDepth L n₁ β)
    let c₂ := simpleHCutoff (if tail₂.isEmpty then n₂ else finiteCriticalDepth M n₂ β)
    ∃ b ∈ centralizerLattice L β k₁ ⊓ centralizerLattice M β k₂,
      ∃ y ∈ simpleHLayer L n₁ β tail₁ (max k₁ c₁.toNat) ⊓
        simpleHLayer M n₂ β tail₂ (max k₂ c₂.toNat), x = b + y := by
  obtain ⟨p, hker, hfix, hpL, hpM⟩ := exists_centralizer_filtration_retraction L M β hfield hL hM
  have hsplit (N : LatticeChain 𝒪[F] F V) (n : ℤ) (tail : List A) (k : ℕ)
      (hp : ∀ d z, z ∈ N.endFiltration d → p z ∈ N.endFiltration d)
      (hx : x ∈ simpleHLayer N n β tail k) :
      let c := simpleHCutoff (if tail.isEmpty then n else finiteCriticalDepth N n β)
      p x ∈ centralizerLattice N β k ∧ x - p x ∈ simpleHLayer N n β tail (max k c.toNat) := by
    let c := simpleHCutoff (if tail.isEmpty then n else finiteCriticalDepth N n β)
    have hem : p x ∈ N.endFiltration k := hp _ _ hx.2
    have hcentral : p x ∈ centralizerLattice N β 0 :=
      ⟨N.endFiltration_antitone (by positivity : (0 : ℤ) ≤ (k : ℤ)) hem, hker x⟩
    refine ⟨⟨hem, hker x⟩, sub_mem hx.1 (centralizerLattice_le_simpleHLattice N n β tail hcentral), ?_⟩
    obtain ⟨b, hb, y, hy, hxy⟩ := Submodule.mem_sup.mp
      (simpleHLattice_le_centralizer_sup N n β tail hx.1)
    have hpby : p x = b + p y := by rw [← hxy, map_add, hfix b hb.2]
    have hdiff : x - p x = y - p y := by rw [hpby, ← hxy]; abel
    have hk : x - p x ∈ N.endFiltration k := sub_mem hx.2 hem
    have hc : x - p x ∈ N.endFiltration c := hdiff ▸ sub_mem hy (hp _ _ hy)
    by_cases hck : c.toNat ≤ k
    · rwa [max_eq_left hck]
    · have hpos : 0 ≤ c := by omega
      rw [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hck)), Int.toNat_of_nonneg hpos]
      exact hc
  obtain ⟨hb₁, hy₁⟩ := hsplit L n₁ tail₁ k₁ hpL hx₁
  obtain ⟨hb₂, hy₂⟩ := hsplit M n₂ tail₂ k₂ hpM hx₂
  exact ⟨p x, ⟨hb₁, hb₂⟩, x - p x, ⟨hy₁, hy₂⟩, by abel⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Relative filtered units lie in the simple-character group at that depth. -/
theorem relativeUnitFiltration_le_simpleHGroup (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) (k : ℕ) :
    relativeUnitFiltration L β k ≤ simpleHGroup L n β tail k := by
  intro g hg
  refine Subgroup.subset_closure ⟨hg.2, centralizerLattice_le_simpleHLattice L n β tail ?_⟩
  refine ⟨hg.2.1, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, StratumEquivalence.adjointMap_apply, sub_eq_zero]
  exact hg.1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem one_mem_simpleHLattice (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) : (1 : A) ∈ simpleHLattice L n β tail := by
  apply centralizerLattice_le_simpleHLattice
  exact ⟨L.order.one_mem, by simp [StratumEquivalence.adjointMap_apply]⟩

/-- On chains whose simple-character groups are the literal filtered carriers,
their intersection factors through the common relative unit group and the common
subgroup at the two upper cutoffs. -/
theorem exists_simpleHGroup_inf_factorization (L M : LatticeChain 𝒪[F] F V)
    (n₁ n₂ : ℤ) (β : A) (tail₁ tail₂ : List A) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hfield : IsField (elementAlgebra β))
    (hL : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hfield.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hcar₁ : ∀ {g}, g ∈ simpleHGroup L n₁ β tail₁ k₁ → (g : A) ∈ simpleHLattice L n₁ β tail₁)
    (hcar₂ : ∀ {g}, g ∈ simpleHGroup M n₂ β tail₂ k₂ → (g : A) ∈ simpleHLattice M n₂ β tail₂)
    {g : G} (hg₁ : g ∈ simpleHGroup L n₁ β tail₁ k₁)
    (hg₂ : g ∈ simpleHGroup M n₂ β tail₂ k₂) :
    let c₁ := simpleHCutoff (if tail₁.isEmpty then n₁ else finiteCriticalDepth L n₁ β)
    let c₂ := simpleHCutoff (if tail₂.isEmpty then n₂ else finiteCriticalDepth M n₂ β)
    ∃ u ∈ relativeUnitFiltration L β k₁ ⊓ relativeUnitFiltration M β k₂,
      ∃ v ∈ simpleHGroup L n₁ β tail₁ (max k₁ c₁.toNat) ⊓
        simpleHGroup M n₂ β tail₂ (max k₂ c₂.toNat), g = u * v := by
  let c₁ := simpleHCutoff (if tail₁.isEmpty then n₁ else finiteCriticalDepth L n₁ β)
  let c₂ := simpleHCutoff (if tail₂.isEmpty then n₂ else finiteCriticalDepth M n₂ β)
  have hg₁' := simpleHGroup_le_unitFiltration L n₁ β tail₁ k₁ hg₁
  have hg₂' := simpleHGroup_le_unitFiltration M n₂ β tail₂ k₂ hg₂
  have hx₁ : (g : A) - 1 ∈ simpleHLayer L n₁ β tail₁ k₁ :=
    ⟨sub_mem (hcar₁ hg₁) (one_mem_simpleHLattice L n₁ β tail₁), hg₁'.2.2⟩
  have hx₂ : (g : A) - 1 ∈ simpleHLayer M n₂ β tail₂ k₂ :=
    ⟨sub_mem (hcar₂ hg₂) (one_mem_simpleHLattice M n₂ β tail₂), hg₂'.2.2⟩
  obtain ⟨b, ⟨hb₁, hb₂⟩, y, ⟨hy₁, hy₂⟩, hsum⟩ :=
    exists_simpleHLayer_inf_decomposition L M n₁ n₂ β tail₁ tail₂ k₁ k₂ hfield hL hM hx₁ hx₂
  obtain ⟨u, hu₁, hu⟩ := L.exists_mem_unitFiltration hk₁ hb₁.1
  obtain ⟨u', hu', hval'⟩ := M.exists_mem_unitFiltration hk₂ hb₂.1
  have hu₂ : u ∈ M.unitFiltration k₂ := (Units.ext (hu.trans hval'.symm) : u = u') ▸ hu'
  have hcomm : u ∈ centralizerUnitGroup β := by
    change Commute β (u : A)
    rw [hu]
    apply (Commute.one_right β).add_right
    have h := hb₁.2
    rwa [SetLike.mem_coe, LinearMap.mem_ker, StratumEquivalence.adjointMap_apply, sub_eq_zero] at h
  have hu₁' : u ∈ relativeUnitFiltration L β k₁ := ⟨hcomm, hu₁⟩
  have hu₂' : u ∈ relativeUnitFiltration M β k₂ := ⟨hcomm, hu₂⟩
  let v := u⁻¹ * g
  have hv : (v : A) - 1 = ((u⁻¹ : G) : A) * y := by
    have hdiff : (g : A) - (u : A) = y := by
      rw [hu, ← sub_sub, hsum, add_comm b y, add_sub_cancel_right]
    simp only [v, Units.val_mul, ← hdiff, mul_sub, Units.inv_mul]
  have hv₁ : v ∈ simpleHGroup L n₁ β tail₁ k₁ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (relativeUnitFiltration_le_simpleHGroup L n₁ β tail₁ k₁ hu₁')) hg₁
  have hv₂ : v ∈ simpleHGroup M n₂ β tail₂ k₂ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ k₂ hu₂')) hg₂
  have hF₁ := simpleHGroup_le_unitFiltration L n₁ β tail₁ k₁ hv₁
  have hF₂ := simpleHGroup_le_unitFiltration M n₂ β tail₂ k₂ hv₂
  have h₁ : v ∈ simpleHGroup L n₁ β tail₁ (max k₁ c₁.toNat) := by
    refine Subgroup.subset_closure ⟨⟨hF₁.1, hF₁.2.1, ?_⟩, hcar₁ hv₁⟩
    rw [hv]
    simpa only [zero_add] using L.mul_mem_endFiltration (m := 0) hu₁.2.1 hy₁.2
  have h₂ : v ∈ simpleHGroup M n₂ β tail₂ (max k₂ c₂.toNat) := by
    refine Subgroup.subset_closure ⟨⟨hF₂.1, hF₂.2.1, ?_⟩, hcar₂ hv₂⟩
    rw [hv]
    simpa only [zero_add] using M.mul_mem_endFiltration (m := 0) hu₂.2.1 hy₂.2
  exact ⟨u, ⟨hu₁', hu₂'⟩, v, ⟨h₁, h₂⟩, by simp [v]⟩

end Langlands.BushnellKutzko
