import Langlands.BushnellKutzko.LatticeChainLayerCommutation
import Langlands.BushnellKutzko.SubfieldValuationShifts

/-! # Extension residue scalars on the successive lattice quotients -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F] (E : Type uE) [Field E] [Algebra F E]

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E
local notation "kₑ[" F "," E "]" => ResidueField (subfieldIntegers F E)

section ResidueEquivalence

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]]

/-- The quotient in the minimality statement agrees with the residue field of the DVR. -/
def subfieldResidueEquiv : subfieldResidueRing F E ≃ₐ[𝒪[F]] kₑ[F,E] :=
  Ideal.quotientEquivAlgOfEq 𝒪[F] (subfieldMaximalIdeal_eq F E)

@[simp] theorem subfieldResidueEquiv_mk (a : 𝒪ₑ[F,E]) :
    subfieldResidueEquiv E (Ideal.Quotient.mk (subfieldMaximalIdeal F E) a) = residue _ a :=
  rfl

end ResidueEquivalence

namespace LatticeChain

variable {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- The homomorphism from the units of a normalizing subfield into the stabilizer. -/
def subfieldStabilizer : Eˣ →* 𝓛.stabilizer :=
  (subfieldUnits F E V).codRestrict 𝓛.stabilizer hE

@[simp] theorem subfieldStabilizer_apply (a : Eˣ) (v : V) :
    ((𝓛.subfieldStabilizer E hE a).val : Module.End F V) v = (a : E) • v := rfl

@[simp] theorem subfieldStabilizer_shift (a : Eˣ) :
    𝓛.stabilizerValuation (𝓛.subfieldStabilizer E hE a) = (𝓛.fieldShift E hE a).toAdd := rfl

/-- The corresponding stabilizer of a layer family, viewed as a subgroup of the field units. -/
def subfieldLayerCommutingSubgroup (D : ∀ i : ℤ, Module.End 𝒪[F] (𝓛.Layer i)) : Subgroup Eˣ :=
  (𝓛.layerCommutingSubgroup D).comap (𝓛.subfieldStabilizer E hE)

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsDiscreteValuationRing 𝒪ₑ[F,E]]

/-- The successive quotient with its residue scalar structure over the extension. -/
@[instance_reducible]
def subfieldLayerResidueModule (i : ℤ) : Module kₑ[F,E] (𝓛.Layer i) :=
  inferInstanceAs (Module kₑ[F,E] ((𝓛.subfieldChain E hE).Layer i))

local notation "layerClass(" L "," i "," v "," hv ")" => LatticeChain.intervalMk L i (i + 1) v hv

/-- Residue scalar multiplication is computed on an integral representative. -/
theorem subfieldLayer_residue_smul_mk (i : ℤ) (a : 𝒪ₑ[F,E]) (v : V) (hv : v ∈ 𝓛.lattice i) :
    letI := 𝓛.subfieldLayerResidueModule E hE i
    residue _ a • layerClass(𝓛,i,v,hv) =
      layerClass(𝓛,i,(a : E) • v,𝓛.subfieldInteger_smul_mem E hE i a hv) := rfl

/-- The base integer action is the restriction of the extension residue action. -/
theorem subfieldLayerResidueTower (i : ℤ) :
    letI := 𝓛.subfieldLayerResidueModule E hE i
    IsScalarTower 𝒪[F] kₑ[F,E] (𝓛.Layer i) := by
  let := 𝓛.subfieldLayerResidueModule E hE i
  apply IsScalarTower.of_algebraMap_smul
  intro a q
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  change residue (𝒪ₑ[F,E]) (algebraMap 𝒪[F] 𝒪ₑ[F,E] a) • layerClass(𝓛,i,v,hv) =
    layerClass(𝓛,i,a • v,(𝓛.lattice i).smul_mem a hv)
  rw [𝓛.subfieldLayer_residue_smul_mk E hE, intervalMk_eq_iff]
  change algebraMap F E (a : F) • v - (a : F) • v ∈ 𝓛.lattice (i + 1)
  rw [algebraMap_smul, sub_self]
  exact zero_mem _

/-- Translation by a field unit respects the extension residue scalars. -/
theorem subfieldLayerEquiv_residue_smul (a : Eˣ) {i j : ℤ}
    (h : j = i + 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E hE a))
    (c : kₑ[F,E]) (q : 𝓛.Layer i) :
    letI := 𝓛.subfieldLayerResidueModule E hE i
    letI := 𝓛.subfieldLayerResidueModule E hE j
    𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE a) i j h (c • q) =
      c • 𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE a) i j h q := by
  let := 𝓛.subfieldLayerResidueModule E hE i
  let := 𝓛.subfieldLayerResidueModule E hE j
  obtain ⟨d, rfl⟩ := residue_surjective c
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rw [𝓛.subfieldLayer_residue_smul_mk E hE, stabilizerLayerEquiv_mk, stabilizerLayerEquiv_mk,
    𝓛.subfieldLayer_residue_smul_mk E hE, intervalMk_eq_iff]
  simp only [subfieldStabilizer_apply, smul_comm (a : E) (d : E), sub_self, zero_mem]

/-- The extension residue scalars which commute with a given layer family. -/
def commutingResidueScalars (D : ∀ i : ℤ, Module.End 𝒪[F] (𝓛.Layer i)) :
    Subalgebra 𝒪[F] kₑ[F,E] where
  carrier := {c | ∀ (i : ℤ) (q : 𝓛.Layer i),
    letI := 𝓛.subfieldLayerResidueModule E hE i
    c • D i q = D i (c • q)}
  add_mem' := by
    intro a b ha hb i q
    let := 𝓛.subfieldLayerResidueModule E hE i
    change (a + b) • D i q = D i ((a + b) • q)
    rw [add_smul, add_smul, map_add, ha i q, hb i q]
  mul_mem' := by
    intro a b ha hb i q
    let := 𝓛.subfieldLayerResidueModule E hE i
    change (a * b) • D i q = D i ((a * b) • q)
    rw [mul_smul, mul_smul, hb i q, ha i (b • q)]
  zero_mem' := by
    intro i q
    let := 𝓛.subfieldLayerResidueModule E hE i
    change (0 : kₑ[F,E]) • D i q = D i ((0 : kₑ[F,E]) • q)
    simp only [zero_smul, map_zero]
  one_mem' := by
    intro i q
    let := 𝓛.subfieldLayerResidueModule E hE i
    change (1 : kₑ[F,E]) • D i q = D i ((1 : kₑ[F,E]) • q)
    simp only [one_smul]
  algebraMap_mem' := by
    intro a i q
    let := 𝓛.subfieldLayerResidueModule E hE i
    have := 𝓛.subfieldLayerResidueTower E hE i
    change (algebraMap 𝒪[F] kₑ[F,E] a) • D i q = D i ((algebraMap 𝒪[F] kₑ[F,E] a) • q)
    rw [algebraMap_smul, algebraMap_smul, map_smul]

/-- The layer action of an integer-ring unit is scalar multiplication by its residue. -/
theorem subfieldLayerEquiv_integerUnit (u : 𝒪ₑ[F,E]ˣ) (i : ℤ)
    (h : i = i + 𝓛.stabilizerValuation (𝓛.subfieldStabilizer E hE (subfieldIntegerUnits E u)))
    (q : 𝓛.Layer i) :
    letI := 𝓛.subfieldLayerResidueModule E hE i
    𝓛.stabilizerLayerEquiv (𝓛.subfieldStabilizer E hE (subfieldIntegerUnits E u)) i i h q =
      residue _ (u : 𝒪ₑ[F,E]) • q := by
  let := 𝓛.subfieldLayerResidueModule E hE i
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rw [stabilizerLayerEquiv_mk, 𝓛.subfieldLayer_residue_smul_mk E hE]
  rfl

/-- An integer unit intertwines the family exactly when its residue commutes. -/
theorem integerUnit_mem_subfieldLayerCommutingSubgroup_iff
    (D : ∀ i : ℤ, Module.End 𝒪[F] (𝓛.Layer i)) (u : 𝒪ₑ[F,E]ˣ) :
    subfieldIntegerUnits E u ∈ 𝓛.subfieldLayerCommutingSubgroup E hE D ↔
      residue _ (u : 𝒪ₑ[F,E]) ∈ 𝓛.commutingResidueScalars E hE D := by
  let g := 𝓛.subfieldStabilizer E hE (subfieldIntegerUnits E u)
  have hg : 𝓛.stabilizerValuation g = 0 := 𝓛.fieldShift_integerUnit E hE u
  change 𝓛.LayerFamilyCommutes D g ↔ _
  constructor
  · intro h i q
    have hh := h i i (by rw [hg, add_zero]) q
    rwa [𝓛.subfieldLayerEquiv_integerUnit E hE, 𝓛.subfieldLayerEquiv_integerUnit E hE] at hh
  · intro h i j hj
    have heq : j = i := hj.trans (by rw [hg, add_zero])
    revert hj
    subst j
    intro hj q
    rw [𝓛.subfieldLayerEquiv_integerUnit E hE, 𝓛.subfieldLayerEquiv_integerUnit E hE]
    exact h i q

end LatticeChain

end Langlands.BushnellKutzko
