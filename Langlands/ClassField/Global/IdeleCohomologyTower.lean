import Langlands.ClassField.Global.IdeleCoefficientSequence
import Langlands.ClassField.Global.CohomologyTowerProof

/-! # Restriction and inflation on actual idele cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

section Restriction

variable (F K E : Type u) [Field F] [Field K] [Field E] [NumberField E]
  [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

/-- Restriction changes the acting Galois group and keeps the idele coefficients. -/
def ideleRestrictionCoefficients :
    Rep.res (AlgEquiv.restrictScalarsHom F : (E ≃ₐ[K] E) →* (E ≃ₐ[F] E))
      (relativeIdeleRepresentation F E) ⟶ relativeIdeleRepresentation K E :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }

/-- Restriction on the ordinary cohomology of the actual idele representation. -/
abbrev relativeIdeleRestriction (n : ℕ) :
    relativeIdeleCohomology F E n ⟶ relativeIdeleCohomology K E n :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom F)
    (ideleRestrictionCoefficients F K E) n

/-- Quotienting ideles by principal ideles commutes with restriction in every degree. -/
theorem relativeIdeleRestriction_comp_quotient (n : ℕ) :
    relativeIdeleRestriction F K E n ≫ ideleQuotientCohomologyMap K E n =
      ideleQuotientCohomologyMap F E n ≫ relativeIdeleClassRestriction F K E n := by
  rw [relativeIdeleRestriction, ideleQuotientCohomologyMap,
    ideleQuotientCohomologyMap, relativeIdeleClassRestriction,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · rfl

/-- The principal embedding commutes with restriction in every degree. -/
theorem relativeRestriction_comp_principal (n : ℕ) :
    relativeRestriction F K E n ≫ principalIdeleCohomologyMap K E n =
      principalIdeleCohomologyMap F E n ≫ relativeIdeleRestriction F K E n := by
  rw [relativeRestriction, principalIdeleCohomologyMap,
    principalIdeleCohomologyMap, relativeIdeleRestriction,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · rfl

end Restriction

section Inflation

variable (F E L : Type u) [Field F] [Field E] [Field L]
  [NumberField E] [NumberField L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower F E L] [Normal F E]

/-- The actual idele inclusion is equivariant along restriction of automorphisms. -/
theorem ideleInclusion_relativeIdeleAut (σ : L ≃ₐ[F] L) (a : IdeleGroup (𝓞 E) E) :
    ideleInclusion (relativeIdeleAut F E (AlgEquiv.restrictNormalHom E σ) a) =
      relativeIdeleAut F L σ (ideleInclusion a) :=
  Units.ext (adeleInclusion_adeleEquiv _ _
    (fun x => (AlgEquiv.restrictNormal_commutes σ E x).symm) a)

/-- The actual idele inclusion, linear over the lifted integers. -/
def ideleInclusionLinear :
    (relativeIdeleRepresentation F E).V →ₗ[ULift.{u} ℤ]
      (relativeIdeleRepresentation F L).V where
  toFun a := Additive.ofMul
    (ideleInclusion (K := E) (L := L) (@Additive.toMul (IdeleGroup (𝓞 E) E) a))
  map_add' a b := congrArg Additive.ofMul (map_mul (ideleInclusion (K := E) (L := L))
    (@Additive.toMul (IdeleGroup (𝓞 E) E) a) (@Additive.toMul (IdeleGroup (𝓞 E) E) b))
  map_smul' r a := congrArg Additive.ofMul (map_zpow (ideleInclusion (K := E) (L := L))
    (@Additive.toMul (IdeleGroup (𝓞 E) E) a) r.down)

/-- The equivariant coefficient inclusion used for inflation of idele cohomology. -/
def ideleInflationCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom E : (L ≃ₐ[F] L) →* (E ≃ₐ[F] E))
      (relativeIdeleRepresentation F E) ⟶ relativeIdeleRepresentation F L :=
  Rep.ofHom
    { toLinearMap := ideleInclusionLinear F E L
      isIntertwining' σ := by
        ext a
        exact congrArg Additive.ofMul
          (ideleInclusion_relativeIdeleAut F E L σ
            (@Additive.toMul (IdeleGroup (𝓞 E) E) a)) }

/-- Inflation on actual idele cohomology, using the actual idele inclusion. -/
abbrev relativeIdeleInflation (n : ℕ) :
    relativeIdeleCohomology F E n ⟶ relativeIdeleCohomology F L n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (ideleInflationCoefficients F E L) n

/-- Quotienting ideles by principal ideles commutes with inflation in every degree. -/
theorem relativeIdeleInflation_comp_quotient (n : ℕ) :
    relativeIdeleInflation F E L n ≫ ideleQuotientCohomologyMap F L n =
      ideleQuotientCohomologyMap F E n ≫ relativeIdeleClassInflation F E L n := by
  rw [relativeIdeleInflation, ideleQuotientCohomologyMap,
    ideleQuotientCohomologyMap, relativeIdeleClassInflation,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · rfl

/-- The principal embedding commutes with inflation in every degree. -/
theorem relativeInflation_comp_principal (n : ℕ) :
    relativeInflation F E L n ≫ principalIdeleCohomologyMap F L n =
      principalIdeleCohomologyMap F E n ≫ relativeIdeleInflation F E L n := by
  rw [relativeInflation, principalIdeleCohomologyMap,
    principalIdeleCohomologyMap, relativeIdeleInflation,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · ext x
    exact congrArg Additive.ofMul (ideleInclusion_diagonal x.toMul).symm

/-- An idele-class cohomology class represented by ideles remains so after inflation. -/
theorem relativeIdeleClassInflation_mem_quotient_range (n : ℕ)
    {c : relativeIdeleClassCohomology F E n}
    (hc : c ∈ (ideleQuotientCohomologyMap F E n).hom.toAddMonoidHom.range) :
    relativeIdeleClassInflation F E L n c ∈
      (ideleQuotientCohomologyMap F L n).hom.toAddMonoidHom.range := by
  obtain ⟨a, rfl⟩ := hc
  exact ⟨relativeIdeleInflation F E L n a,
    ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F E L n) a⟩

end Inflation

section RestrictionTower

variable (F K L E : Type u) [Field F] [Field K] [Field L] [Field E] [NumberField E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K L] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E]
  [IsScalarTower K L E]

/-- Restriction of idele cohomology is transitive. -/
theorem relativeIdeleRestriction_trans (n : ℕ) :
    relativeIdeleRestriction F K E n ≫ relativeIdeleRestriction K L E n =
      relativeIdeleRestriction F L E n := by
  rw [relativeIdeleRestriction, relativeIdeleRestriction, relativeIdeleRestriction,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · rfl

end RestrictionTower

section InflationTower

variable (F E L M : Type u) [Field F] [Field E] [Field L] [Field M]
  [NumberField E] [NumberField L] [NumberField M]
  [Algebra F E] [Algebra F L] [Algebra F M] [Algebra E L] [Algebra E M] [Algebra L M]
  [IsScalarTower F E L] [IsScalarTower F E M] [IsScalarTower F L M]
  [IsScalarTower E L M] [Normal F E] [Normal F L]

/-- Inflation of idele cohomology is transitive. -/
theorem relativeIdeleInflation_trans (n : ℕ) :
    relativeIdeleInflation F E L n ≫ relativeIdeleInflation F L M n =
      relativeIdeleInflation F E M n := by
  rw [relativeIdeleInflation, relativeIdeleInflation, relativeIdeleInflation,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp F E L M).symm
  · ext x
    exact congrArg Additive.ofMul
      (Units.ext (adeleInclusion_trans (K := E) (L := L) (M := M)
        (@Additive.toMul (IdeleGroup (𝓞 E) E) x)))

end InflationTower

section MixedTower

variable (F K E L : Type u) [Field F] [Field K] [Field E] [Field L]
  [NumberField E] [NumberField L]
  [Algebra F K] [Algebra F E] [Algebra F L] [Algebra K E] [Algebra K L] [Algebra E L]
  [IsScalarTower F K E] [IsScalarTower F K L] [IsScalarTower F E L]
  [IsScalarTower K E L] [Normal F E] [Normal K E]

/-- Inflation of idele cohomology commutes with restriction of the base field. -/
theorem relativeIdeleInflation_restriction (n : ℕ) :
    relativeIdeleInflation F E L n ≫ relativeIdeleRestriction F K L n =
      relativeIdeleRestriction F K E n ≫ relativeIdeleInflation K E L n := by
  rw [relativeIdeleInflation, relativeIdeleRestriction,
    relativeIdeleRestriction, relativeIdeleInflation,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap E L).injective
    change algebraMap E L ((σ.restrictScalars F).restrictNormal E x) =
      algebraMap E L ((σ.restrictNormal E).restrictScalars F x)
    rw [AlgEquiv.restrictNormal_commutes]
    exact (AlgEquiv.restrictNormal_commutes σ E x).symm
  · rfl

end MixedTower

end Langlands.ClassField.Global
