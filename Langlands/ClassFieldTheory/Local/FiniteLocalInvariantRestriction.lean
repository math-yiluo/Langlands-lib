import Langlands.ClassFieldTheory.Local.SpectralUnramifiedInvariant
import Langlands.ClassFieldTheory.Local.SeparableUnramifiedBaseChange
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof

noncomputable section

open Langlands.LocalField Langlands.LocalGalois.Separable ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u

section CocycleSum

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E)

private theorem spectralInvariant_H2π_of_sum
    (c : groupCohomology.cocycles₂ (unitsRepresentation K E)) (b : Kˣ)
    (hc : ∑ i ∈ Finset.range (Module.finrank K E), c (finiteUnramifiedFrobenius K E hE ^ i,
        finiteUnramifiedFrobenius K E hE) = baseUnit K E b) :
    spectralUnramifiedInvariant K E hE (groupCohomology.H2π _ c) =
      rationalClass ((normalizedUnitOrder K (.ofMul b) : ℚ) / Module.finrank K E) := by
  let := FiniteExtension.normedField K E
  let := FiniteExtension.valuativeRel K E
  let := FiniteExtension.isLocalField K E
  let := spectralFiniteExtension_valuativeExtension K E
  let hcont := spectralFiniteExtension_algebraMap_continuous K E
  let he := localRamificationFactor_eq_one_of_arithmeticUnramified K E hE
  let χ := finiteUnramifiedCyclicCoordinate K E hE
  let σ := cyclicCoordinateGenerator χ
  have hσ : σ = finiteUnramifiedFrobenius K E hE := cyclicCoordinateGenerator_finiteUnramified K E hE
  have hsum : ∑ i ∈ Finset.range (Module.finrank K E), c (σ ^ i, σ) = baseUnit K E b := by
    rwa [hσ]
  change (denominatorEquiv _ Module.finrank_pos (localUnramifiedNormOrderEquiv K E hcont he
    (cyclicH2NormEquiv K E σ (cyclicCoordinateGenerator_generates χ)
      (groupCohomology.H2π _ c))) : RationalModIntegers) = _
  rw [UnramifiedBaseChange.cyclicH2NormEquiv_H2π_of_sum K E σ
    (cyclicCoordinateGenerator_generates χ) c b hsum, localUnramifiedNormOrderEquiv_projection,
    denominatorEquiv_intCast]

end CocycleSum

variable (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Algebra K (SeparableClosure L)] [IsScalarTower K L (SeparableClosure L)]
  (j : SeparableClosure K →ₐ[K] SeparableClosure L)
  (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

local notation "M" => unramifiedCompositum K L j E

/-- The map of relative cohomology at a compositum stage, by actual inflation and restriction. -/
def finiteUnramifiedBaseChange : relativeCohomology K E 2 →+ relativeCohomology L M 2 := by
  let := unramifiedCompositumAlgebra K L j E
  let := unramifiedCompositumTower K L j E
  exact (relativeRestriction K L M 2).hom.toAddMonoidHom.comp
    (relativeInflation K E M 2).hom.toAddMonoidHom

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- The finite unramified invariant scales by the whole degree, without a separability premise. -/
theorem spectralUnramifiedInvariant_baseChange (hcont : Continuous (algebraMap K L))
    (hE : ArithmeticUnramified K E) (x : relativeCohomology K E 2) :
    spectralUnramifiedInvariant L M (unramifiedCompositum_unramified K L j E hE)
      (finiteUnramifiedBaseChange K L j E x) =
      Module.finrank K L • spectralUnramifiedInvariant K E hE x := by
  let hM := unramifiedCompositum_unramified K L j E hE
  let := unramifiedCompositumAlgebra K L j E
  let := unramifiedCompositumTower K L j E
  let n := Module.finrank K E
  let m := Module.finrank L M
  let : NeZero n := ⟨Module.finrank_pos.ne'⟩
  let : NeZero m := ⟨Module.finrank_pos.ne'⟩
  let χE := finiteUnramifiedCyclicCoordinate K E hE
  let χM := finiteUnramifiedCyclicCoordinate L M hM
  let χ' : Gal(M/L) →* Multiplicative (ZMod n) :=
    χE.toMonoidHom.comp (unramifiedCompositumRestriction K L j E)
  let σ := finiteUnramifiedFrobenius K E hE
  let τ := finiteUnramifiedFrobenius L M hM
  let f := spectralResidueDegree K L
  have hσ : σ = cyclicCoordinateGenerator χE := (cyclicCoordinateGenerator_finiteUnramified K E hE).symm
  have hτ : τ = cyclicCoordinateGenerator χM := (cyclicCoordinateGenerator_finiteUnramified L M hM).symm
  have ht : (χ' τ).toAdd = (f : ZMod n) := by
    change (χE (unramifiedCompositumRestriction K L j E τ)).toAdd = _
    rw [unramifiedCompositumRestriction_frobenius K L j E hE σ τ
      (finiteUnramifiedFrobenius_residue K E hE) (finiteUnramifiedFrobenius_residue L M hM),
      hσ, map_pow, cyclicCoordinateGenerator, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd,
      nsmul_one]
  have hmt : m • (χ' τ).toAdd = 0 := by
    have h := congrArg (fun y => (χ' y).toAdd) (UnramifiedBaseChange.coordinateGenerator_pow_card χM)
    rw [← hτ] at h
    simpa only [map_pow, toAdd_pow, map_one, toAdd_one] using h
  have hS := UnramifiedBaseChange.carry_sum_telescope (χ' τ).toAdd m
  rw [hmt, ZMod.val_zero, add_zero] at hS
  obtain ⟨a, rfl⟩ := exists_finiteLocal_cyclicClass K E χE x
  let b : Lˣ := Units.map (algebraMap K L) a
  let s := ∑ i ∈ Finset.range m, cyclicCarry (i • (χ' τ).toAdd) (χ' τ).toAdd
  have hsum := UnramifiedBaseChange.cyclicUnitCocycle_sum L M χ' b τ m
  have hbc : finiteUnramifiedBaseChange K L j E (cyclicClass K E χE.toMonoidHom a) =
      cyclicClass L M χ' b :=
    UnramifiedBaseChange.restriction_inflation_cyclicClass K L E M χE.toMonoidHom a
  rw [hbc, cyclicClass, spectralInvariant_H2π_of_sum L M hM _ (b ^ s) hsum]
  change rationalClass ((normalizedUnitOrder L (.ofMul (b ^ s)) : ℚ) / m) =
    Module.finrank K L • spectralUnramifiedInvariant K E hE
      (cyclicClass K E (finiteUnramifiedCyclicCoordinate K E hE).toMonoidHom a)
  rw [spectralUnramifiedInvariant_cyclicClass, ofMul_pow, map_nsmul, nsmul_eq_mul]
  have hf : n * (f / n) + (χ' τ).toAdd.val = f := by
    rw [ht, ZMod.val_natCast]
    exact Nat.div_add_mod _ _
  have hord : (f : ℤ) * normalizedUnitOrder L (.ofMul b) =
      (Module.finrank K L : ℤ) * normalizedUnitOrder K (.ofMul a) := by
    change (spectralResidueDegree K L : ℤ) * normalizedUnitOrder L
      (.ofMul (Units.map (algebraMap K L) a)) = _
    rw [normalizedUnitOrder_map K L, spectralResidueDegree_eq_finrank, ← mul_assoc,
      ← Nat.cast_mul, mul_comm (localResidueDegree K L),
      localRamificationFactor_mul_residueDegree K L hcont]
  exact UnramifiedBaseChange.rationalClass_scaling (NeZero.pos n) (NeZero.pos m) hS hf hord

end Langlands.ClassFieldTheory.Local
