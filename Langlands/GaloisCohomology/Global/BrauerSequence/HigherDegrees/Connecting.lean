import Langlands.ClassFieldTheory.Global.IdeleCohomologyTower
import Langlands.ClassFieldTheory.Global.IdeleCoefficientSequence
import Langlands.GaloisCohomology.Field.FiniteLevel
import Langlands.Cohomology.RestrictedProduct

/-!
# The connecting map of the idèle sequence and inflation

The connecting homomorphism of the long exact sequence of group cohomology is natural for a
change of group together with a morphism of short exact sequences of coefficients
(`groupCohomology_δ_comp_map`). For a tower `F ⊆ E ⊆ L` of number fields with `E / F` and
`L / F` Galois, the inclusions `Eˣ → Lˣ`, `J_E → J_L`, `C_E → C_L` form such a morphism from the
idèle sequence `0 → Eˣ → J_E → C_E → 0` of `Gal(E/F)` to that of `Gal(L/F)`
(`ideleCoefficientSequenceInflation`); hence the connecting maps of the two idèle sequences commute
with inflation (`δ_comp_relativeInflation`). Finally the foundations' inflation between finite
levels of a Galois extension, `unitsInflationOfLE`, is the Library's `relativeInflation`
(`unitsInflationOfLE_eq_relativeInflation`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality

universe u

noncomputable section

section Ideles

variable (F E L : Type u) [Field F] [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L] [Normal F E]

/-- The inflation morphism of idèle sequences: `Eˣ → Lˣ`, `J_E → J_L`, `C_E → C_L`, from the idèle
sequence of `Gal(E/F)` restricted to `Gal(L/F)` to the idèle sequence of `Gal(L/F)`. -/
def ideleCoefficientSequenceInflation :
    (ideleCoefficientSequence F E).map
        (Rep.resFunctor (AlgEquiv.restrictNormalHom E : (L ≃ₐ[F] L) →* (E ≃ₐ[F] E))) ⟶
      ideleCoefficientSequence F L where
  τ₁ := inflationCoefficients F E L
  τ₂ := ideleInflationCoefficients F E L
  τ₃ := ideleClassInflationCoefficients F E L
  comm₁₂ := by
    ext x
    exact congrArg Additive.ofMul (ideleInclusion_diagonal x.toMul).symm
  comm₂₃ := rfl

/-- The connecting maps of the idèle sequences commute with inflation. -/
@[reassoc]
theorem δ_comp_relativeInflation (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ (ideleCoefficientSequence_shortExact F E) i j hij ≫
        relativeInflation F E L j =
      relativeIdeleClassInflation F E L i ≫
        groupCohomology.δ (ideleCoefficientSequence_shortExact F L) i j hij :=
  Cohomology.groupCohomology_δ_comp_map _ (ideleCoefficientSequenceInflation F E L)
    (ideleCoefficientSequence_shortExact F E) (ideleCoefficientSequence_shortExact F L) i j hij

/-- Elementwise form of `δ_comp_relativeInflation`. -/
theorem relativeInflation_δ_apply (i j : ℕ) (hij : i + 1 = j)
    (c : relativeIdeleClassCohomology F E i) :
    relativeInflation F E L j (groupCohomology.δ (ideleCoefficientSequence_shortExact F E) i j hij c) =
      groupCohomology.δ (ideleCoefficientSequence_shortExact F L) i j hij
        (relativeIdeleClassInflation F E L i c) :=
  ConcreteCategory.congr_hom (δ_comp_relativeInflation F E L i j hij) c

end Ideles

section Levels

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] {E E' : IntermediateField K Ω}
  (h : E ≤ E') [Normal K E]

/-- The foundations' inflation `unitsInflationOfLE` between two finite levels `E ≤ E'` is the
Library's `relativeInflation`, for the algebra `E → E'` given by the inclusion. -/
theorem unitsInflationOfLE_eq_relativeInflation (n : ℕ) :
    letI : Algebra E E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
    haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq' rfl
    unitsInflationOfLE h n = relativeInflation K E E' n := by
  let _ : Algebra E E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have _ : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq' rfl
  exact groupCohomology.map_congr rfl rfl n

end Levels

end

end Langlands.GaloisCohomology
