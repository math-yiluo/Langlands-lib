import Langlands.Representation.Exponents.ScalarTargetWeightRestriction
import Langlands.Representation.Plancherel.SplitTorusRealPart
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients

/-! # Restriction to unitary split weights for a square-integrable target -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme

namespace Langlands

universe u uH uV uW

section Parameter

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A pointwise unitary split-torus character has zero normalized real part.
This direction requires no continuity or open-kernel premise. -/
theorem Plancherel.SplitTorus.normalizedRealPart_eq_zero_of_norm
    (hA : IsSplitTorus A.toGrp) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    Plancherel.SplitTorus.normalizedRealPart hA χ = 0 := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A
    (Plancherel.SplitTorus.normalizedRealPart hA χ) (r ⊗ₜ[ℤ] c) = 0
  rw [Plancherel.SplitTorus.pair_normalizedRealPart_tmul]
  change r * (-Real.log ‖(χ (CocharacterUniformizer.latticeSection F A
    (Multiplicative.ofAdd c)) : ℂ)‖ / Real.log (LocalField.residueCardinality F : ℝ)) = 0
  rw [hχ]
  simp

end Parameter

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (hA : IsSplitTorus A.toGrp)
  {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  [WeaklyLocallyCompactSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ H V) (σ : Representation ℂ H W)
  (j : rationalPoints A.toGrp →* H) (hj : ∀ a, j a ∈ Subgroup.center H)

/-- The existing selected-weight restriction specialized to zero normalized
real part on the actual split torus. -/
def splitUnitaryWeightRestriction :
    (ρ.IntertwiningMap σ) →ₗ[ℂ]
      ((selectedWeightPart ρ j hj
        (fun χ => Plancherel.SplitTorus.normalizedRealPart hA χ = 0)).toRepresentation.IntertwiningMap σ) :=
  scalarTargetWeightRestriction ρ σ j hj
    (fun χ => Plancherel.SplitTorus.normalizedRealPart hA χ = 0)

/-- An admissible source and a supplied unitary full-center scalar character
of the target make this literal restriction injective. -/
theorem splitUnitaryWeightRestriction_injective
    (hρ : IsAdmissible ρ) (c : UnitaryCentralCharacter σ) :
    Function.Injective (splitUnitaryWeightRestriction hA ρ σ j hj) := by
  let ψ : rationalPoints A.toGrp →* ℂˣ :=
    c.character.comp (j.codRestrict (Subgroup.center H) hj)
  apply scalarTargetWeightRestriction_injective ρ σ j hj hρ ψ
    (fun a w => c.acts ⟨j a, hj a⟩ w)
  exact Plancherel.SplitTorus.normalizedRealPart_eq_zero_of_norm hA ψ
    (fun a => c.norm_eq_one ⟨j a, hj a⟩)

/-- The whole intertwining space has cardinal rank bounded by the one from
the selected unitary split weights, for a target with unitary central action. -/
theorem hom_rank_le_splitUnitaryWeights
    (hρ : IsAdmissible ρ) (c : UnitaryCentralCharacter σ) :
    Module.rank ℂ (ρ.IntertwiningMap σ) ≤
      Module.rank ℂ
        ((selectedWeightPart ρ j hj
          (fun χ => Plancherel.SplitTorus.normalizedRealPart hA χ = 0)).toRepresentation.IntertwiningMap σ) :=
  LinearMap.rank_le_of_injective (splitUnitaryWeightRestriction hA ρ σ j hj)
    (splitUnitaryWeightRestriction_injective hA ρ σ j hj hρ c)

section SquareIntegrable

variable (C : Subgroup H) [C.Normal]
  (hC : C ≤ Subgroup.center H) [MeasurableSpace (H ⧸ C)]
  (qMeasure : MeasureTheory.Measure (H ⧸ C)) [MeasureTheory.Measure.IsHaarMeasure qMeasure]

/-- The target's square-integrability predicate itself supplies the unitary
central scalar action needed for this rank restriction. No temperedness
comparison or target irreducibility is required for this step. -/
theorem hom_rank_le_splitUnitaryWeights_of_squareIntegrable
    (hρ : IsAdmissible ρ)
    (hσ : Plancherel.IsSquareIntegrableModCentralSubgroup C hC σ qMeasure) :
    Module.rank ℂ (ρ.IntertwiningMap σ) ≤
      Module.rank ℂ
        ((selectedWeightPart ρ j hj
          (fun χ => Plancherel.SplitTorus.normalizedRealPart hA χ = 0)).toRepresentation.IntertwiningMap σ) := by
  obtain ⟨_, c, _⟩ := hσ
  exact hom_rank_le_splitUnitaryWeights hA ρ σ j hj hρ c

end SquareIntegrable

end Langlands
