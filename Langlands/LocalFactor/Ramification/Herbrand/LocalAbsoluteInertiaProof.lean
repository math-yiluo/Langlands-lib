import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteStatement

/-!
# The index-zero absolute upper group

Finite and closure integers use the same spectral norm on each finite subfield.
This identifies the residue test for inertia with the defining finite tests at zero.
-/

noncomputable section

open IsLocalRing ValuativeRel

namespace Langlands.Ramification.Local

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

private local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
private local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
private local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

private theorem finiteValuation_isEquiv (L : FiniteGaloisIntermediateField K Ω) :
    letI := (localTopologicalData K L).valuativeRel
    (valuation L).IsEquiv ((LocalGalois.spectralValuation K Ω).comap (algebraMap L Ω)) := by
  let := LocalField.canonicalValuativeRel K L
  let : (LocalField.canonicalValuation K L).Compatible :=
    Valuation.Compatible.ofValuation _
  refine (ValuativeRel.isEquiv (valuation L) (LocalField.canonicalValuation K L)).trans ?_
  intro x y
  change spectralNorm K L x ≤ spectralNorm K L y ↔
    spectralNorm K Ω (algebraMap L Ω x) ≤ spectralNorm K Ω (algebraMap L Ω y)
  rw [spectralNorm.eq_of_tower (L := Ω) x, spectralNorm.eq_of_tower (L := Ω) y]

private theorem mem_finiteIntegers_iff (L : FiniteGaloisIntermediateField K Ω) (x : L) :
    x ∈ (localTopologicalData K L).Integers ↔ spectralNorm K Ω (x : Ω) ≤ 1 :=
  (finiteValuation_isEquiv K Ω L).le_one_iff_le_one

private theorem mem_finiteMaximalIdeal_iff (L : FiniteGaloisIntermediateField K Ω)
    (x : (localTopologicalData K L).Integers) :
    x ∈ maximalIdeal (localTopologicalData K L).Integers ↔
      spectralNorm K Ω ((x : L) : Ω) < 1 := by
  let := (localTopologicalData K L).valuativeRel
  change x ∈ maximalIdeal (valuation L).integer ↔ _
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact (finiteValuation_isEquiv K Ω L).lt_one_iff_lt_one

private theorem finiteRestriction_mem_upperZero_iff (L : FiniteGaloisIntermediateField K Ω)
    (σ : Ω ≃ₐ[K] Ω) :
    absoluteFiniteRestriction K Ω L σ ∈ localUpperRamificationGroup K L 0 ↔
      ∀ x : L, spectralNorm K Ω (x : Ω) ≤ 1 →
        spectralNorm K Ω (σ (x : Ω) - (x : Ω)) < 1 := by
  rw [localUpperRamificationGroup, upperRamificationGroup_zero, ← lowerRamificationGroup_zero,
    mem_lowerRamificationGroup]
  simp only [zero_add, pow_one]
  let T := localTopologicalData K L
  let τ := absoluteFiniteRestriction K Ω L σ
  have hdiff (x : T.Integers) :
      integerAutomorphism T K τ x - x ∈ maximalIdeal T.Integers ↔
        spectralNorm K Ω (σ (x : Ω) - (x : Ω)) < 1 := by
    have h := mem_finiteMaximalIdeal_iff K Ω L (integerAutomorphism T K τ x - x)
    change _ ↔ spectralNorm K Ω (algebraMap L Ω (τ (x : L) - (x : L))) < 1 at h
    rw [map_sub, show algebraMap L Ω (τ (x : L)) = σ (algebraMap L Ω (x : L))
      from σ.restrictNormal_commutes L (x : L)] at h
    exact h
  constructor
  · intro h x hx
    let a : T.Integers := ⟨x, (mem_finiteIntegers_iff K Ω L x).mpr hx⟩
    exact (hdiff a).mp (h a)
  · intro h x
    exact (hdiff x).mpr (h x ((mem_finiteIntegers_iff K Ω L x).mp x.property))

/-- The absolute upper group at zero equals the inertia subgroup of the specified
separable closure. -/
theorem absoluteUpperInertia : AbsoluteUpperInertia K Ω := by
  unfold AbsoluteUpperInertia
  ext σ
  change (σ ∈ ⨅ L : FiniteGaloisIntermediateField K Ω,
    (localUpperRamificationGroup K L 0).comap (absoluteFiniteRestriction K Ω L).toMonoidHom) ↔
      σ ∈ LocalGalois.inertia K Ω
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, ContinuousMonoidHom.coe_toMonoidHom,
    LocalGalois.mem_inertia_iff]
  have hresidue (x : LocalGalois.SepClosed.closureIntegers K Ω) :
      residue _ (LocalGalois.integerAut K Ω σ x) = residue _ x ↔
        spectralNorm K Ω (σ (x : Ω) - (x : Ω)) < 1 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact (LocalGalois.spectralValuation K Ω).mem_maximalIdeal_iff
  constructor
  · intro h x
    let L := FiniteGaloisIntermediateField.adjoin K ({(x : Ω)} : Set Ω)
    have hxL : (x : Ω) ∈ L.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K _ rfl
    exact (hresidue x).mpr
      ((finiteRestriction_mem_upperZero_iff K Ω L σ).mp (h L) ⟨x, hxL⟩ x.property)
  · intro h L
    apply (finiteRestriction_mem_upperZero_iff K Ω L σ).mpr
    intro x hx
    exact (hresidue ⟨(x : Ω), hx⟩).mp (h ⟨(x : Ω), hx⟩)

end Langlands.Ramification.Local
