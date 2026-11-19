import Langlands.BushnellKutzko.SubfieldChainLayers

/-! # Lifting layer maps to endomorphisms linear over the normalizing field -/

noncomputable section

open ValuativeRel IsLocalRing IsDiscreteValuationRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V) (E : Type uE) [Field E] [Algebra F E]
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

/-- Multiplication by the base uniformizer is the same stabilizer unit in the field action. -/
theorem subfieldStabilizer_baseUniformizer {π : 𝒪[F]} (hπ : Irreducible π) :
    𝓛.subfieldStabilizer E hE (baseIntegerUnit E hπ.ne_zero) = 𝓛.uniformizerStabilizer hπ := by
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  change algebraMap F E (π : F) • v = (π : F) • v
  exact algebraMap_smul E (π : F) v

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

/-- The period of the extension lattice chain is the original chain shift of its uniformizer. -/
theorem subfieldChain_period_eq_shift {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ) :
    ((𝓛.subfieldChain E hE).period : ℤ) =
      (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd := by
  let L := 𝓛.subfieldChain E hE
  let g := L.uniformizerStabilizer hϖ
  let d := (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  have hm (v : V) : (ϖ : E) • v ∈ 𝓛.lattice (0 + (L.period : ℤ)) ↔ v ∈ 𝓛.lattice 0 := by
    have h := L.mem_lattice_stabilizer_iff g 0 v
    rw [uniformizerStabilizer_shift] at h
    exact h
  have hd (v : V) : (ϖ : E) • v ∈ 𝓛.lattice (0 + d) ↔ v ∈ 𝓛.lattice 0 :=
    𝓛.mem_lattice_fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero) 0
  have heq : 𝓛.lattice (0 + (L.period : ℤ)) = 𝓛.lattice (0 + d) := by
    ext v
    have hϖ₀ : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have h := (hm ((ϖ : E)⁻¹ • v)).trans (hd ((ϖ : E)⁻¹ • v)).symm
    simpa only [smul_smul, mul_inv_cancel₀ hϖ₀, one_smul] using h
  exact add_left_cancel (𝓛.injective heq)

/-- A family intertwining every field unit lifts to an endomorphism linear over that field. -/
theorem exists_subfield_lift_layers (D : ∀ i : ℤ, Module.End 𝒪[F] (𝓛.Layer i))
    (hD : ∀ a : Eˣ, a ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D) :
    ∃ (y : Module.End E V) (hy : y.restrictScalars F ∈ 𝓛.order),
      ∀ i, 𝓛.layerAction ⟨y.restrictScalars F, hy⟩ i = D i := by
  let L := 𝓛.subfieldChain E hE
  have hscalar (c : ResidueField 𝒪ₑ[F,E]) : c ∈ 𝓛.commutingResidueScalars E hE D := by
    by_cases hc : c = 0
    · rw [hc]
      exact zero_mem _
    · obtain ⟨a, rfl⟩ := residue_surjective c
      obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit a).mp hc
      exact (𝓛.integerUnit_mem_subfieldLayerCommutingSubgroup_iff E hE D u).mp (hD _)
  let DE (i : ℤ) : Module.End 𝒪ₑ[F,E] (L.Layer i) := by
    let := 𝓛.subfieldLayerResidueModule E hE i
    refine { (D i).toAddMonoidHom with map_smul' := fun a q => ?_ }
    change D i (residue 𝒪ₑ[F,E] a • q) = residue 𝒪ₑ[F,E] a • D i q
    exact (hscalar (residue _ a) i q).symm
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
  let a := subfieldIntegerUnit E hϖ.ne_zero
  let g := 𝓛.subfieldStabilizer E hE a
  let gE := L.uniformizerStabilizer hϖ
  have hs : L.stabilizerValuation gE = 𝓛.stabilizerValuation g := by
    rw [L.uniformizerStabilizer_shift hϖ]
    exact 𝓛.subfieldChain_period_eq_shift E hE hϖ
  have hcomp : L.LayerFamilyCommutes DE gE := by
    intro i j hj q
    have hj' : j = i + 𝓛.stabilizerValuation g := hj.trans (congrArg (i + ·) hs)
    have hcompare (w : L.Layer i) : L.stabilizerLayerEquiv gE i j hj w =
        𝓛.stabilizerLayerEquiv g i j hj' w := by
      obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) w
      have hvE : v ∈ L.lattice i := hv
      exact (L.stabilizerLayerEquiv_mk gE hj v hvE).trans
        (𝓛.stabilizerLayerEquiv_mk g hj' v hv).symm
    rw [hcompare, hcompare]
    exact hD a i j hj' q
  obtain ⟨y, hy⟩ := L.exists_order_lift_layers hϖ DE hcomp
  have hyF : y.val.restrictScalars F ∈ 𝓛.order := 𝓛.mem_order.mpr (L.mem_order.mp y.prop)
  refine ⟨y.val, hyF, fun i => LinearMap.ext fun q => ?_⟩
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  exact LinearMap.congr_fun (hy i) (L.intervalMk i (i + 1) v hv)

end Langlands.BushnellKutzko.LatticeChain

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- A layer family commuting with the normalizing field units lifts over that field. -/
def SubfieldLayerLiftStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    (D : ∀ i : ℤ, Module.End 𝒪[F] (𝓛.Layer i)),
    (∀ a : Eˣ, a ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D) →
      ∃ (y : Module.End E V) (hy : y.restrictScalars F ∈ 𝓛.order),
        ∀ i, 𝓛.layerAction ⟨y.restrictScalars F, hy⟩ i = D i

theorem subfieldLayerLift : SubfieldLayerLiftStatement.{uF,uV,uE} := by
  intro F _ _ _ _ V _ _ E _ _ _ _ 𝓛 hE D hD
  have := 𝓛.finiteDimensional_subfield E
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := subfieldIntegers_isFractionRing F E
  exact 𝓛.exists_subfield_lift_layers E hE D hD

end Langlands.BushnellKutzko
