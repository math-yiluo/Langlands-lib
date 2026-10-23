import Langlands.ClassField.Global.IdeleTotalTower

/-! # Idele-class invariants represented in a chosen extension -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.ClassFieldTheory.Local CategoryTheory
open Langlands.Global.AdelicFunctoriality

universe u

section Extension

variable (F E L : Type u) [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- Classes whose inflation to the chosen extension is represented by idele cohomology. -/
def ideleClassRegularSubgroup : AddSubgroup (relativeIdeleClassCohomology F E 2) :=
  (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.range.comap
    (relativeIdeleClassInflation F E L 2).hom.toAddMonoidHom

omit [NumberField F] [IsGalois F L] in
theorem mem_ideleClassRegularSubgroup_iff (c : relativeIdeleClassCohomology F E 2) :
    c ∈ ideleClassRegularSubgroup F E L ↔
      ∃ a : relativeIdeleCohomology F L 2,
        ideleQuotientCohomologyMap F L 2 a = relativeIdeleClassInflation F E L 2 c :=
  Iff.rfl

/-- Inflation, with its codomain restricted to the quotient-map image. -/
def ideleClassRegularInflation :
    ideleClassRegularSubgroup F E L →+
      (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.range where
  toFun c := ⟨relativeIdeleClassInflation F E L 2 c, c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext ((relativeIdeleClassInflation F E L 2).hom.map_add c.val d.val)

omit [NumberField F] [IsGalois F L] in
/-- Classes already represented over the lower field belong to the chosen subgroup. -/
theorem quotient_range_le_ideleClassRegularSubgroup :
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.range ≤
      ideleClassRegularSubgroup F E L := by
  intro c hc
  exact relativeIdeleClassInflation_mem_quotient_range F E L 2 hc

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
  (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
  (hrec : ∀ x : relativeCohomology F L 2, Reciprocity.SumOfInvariantsVanishes I x)

/-- The invariant of a class represented after inflation to the chosen extension. -/
def ideleClassInvariantViaExtension :
    ideleClassRegularSubgroup F E L →+ RationalModIntegers :=
  (ideleClassInvariantOnQuotientRange I hI wf wi hrec).comp
    (ideleClassRegularInflation F E L)

/-- Any idele representative of the inflated class computes its invariant. -/
theorem ideleClassInvariantViaExtension_eq_total
    (c : ideleClassRegularSubgroup F E L) (a : relativeIdeleCohomology F L 2)
    (ha : ideleQuotientCohomologyMap F L 2 a =
      relativeIdeleClassInflation F E L 2 c) :
    ideleClassInvariantViaExtension F E L I hI wf wi hrec c =
      totalIdeleInvariant I hI wf wi a := by
  change ideleClassInvariantOnQuotientRange I hI wf wi hrec
    (ideleClassRegularInflation F E L c) = _
  have h : ideleClassRegularInflation F E L c =
      (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.rangeRestrict a :=
    Subtype.ext ha.symm
  rw [h, ideleClassInvariantOnQuotientRange_apply_quotient]

end Extension

section Tower

variable (F E L M : Type u) [Field F] [Field E] [Field L] [Field M]
  [NumberField F] [NumberField E] [NumberField L] [NumberField M]
  [Algebra F E] [Algebra F L] [Algebra F M]
  [Algebra E L] [Algebra E M] [Algebra L M]
  [IsScalarTower F E L] [IsScalarTower F E M]
  [IsScalarTower F L M] [IsScalarTower E L M]
  [IsGalois F E] [IsGalois F L] [IsGalois F M]

/-- Enlarging the chosen extension preserves representability by ideles. -/
theorem ideleClassRegularSubgroup_le :
    ideleClassRegularSubgroup F E L ≤ ideleClassRegularSubgroup F E M := by
  intro c hc
  change relativeIdeleClassInflation F E M 2 c ∈
    (ideleQuotientCohomologyMap F M 2).hom.toAddMonoidHom.range
  rw [← ideleClassInflationTransitivity F E L M 2 c]
  exact relativeIdeleClassInflation_mem_quotient_range F L M 2 hc

variable
  (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
  (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove M v)
  (hf : ∀ v, (wf' v).1.asIdeal.LiesOver (wf v).1.asIdeal)
  (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
  (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove M v)
  (hi : ∀ v, (wi' v).1.comap (algebraMap L M) = (wi v).1)
  (hrec : ∀ x : relativeCohomology F L 2, Reciprocity.SumOfInvariantsVanishes I x)
  (hrec' : ∀ x : relativeCohomology F M 2, Reciprocity.SumOfInvariantsVanishes I x)

include hInf hf hi in
/-- The invariant is unchanged when the chosen representing extension is enlarged. -/
theorem ideleClassInvariantViaExtension_tower
    (c : ideleClassRegularSubgroup F E L) :
    ideleClassInvariantViaExtension F E M I hI wf' wi' hrec'
        ⟨c, ideleClassRegularSubgroup_le F E L M c.property⟩ =
      ideleClassInvariantViaExtension F E L I hI wf wi hrec c := by
  change ideleClassInvariantOnQuotientRange I hI wf' wi' hrec'
    (ideleClassRegularInflation F E M _) = _
  have h : ideleClassRegularInflation F E M
        ⟨c, ideleClassRegularSubgroup_le F E L M c.property⟩ =
      ideleQuotientRangeInflation (ideleClassRegularInflation F E L c) :=
    Subtype.ext (ideleClassInflationTransitivity F E L M 2 c).symm
  rw [h, ideleClassInvariantOnQuotientRange_inflation I hI wf wi hrec
    hInf wf' hf wi' hi hrec']
  rfl

end Tower

section CommonOverfield

variable {F L₁ L₂ M : Type u} [Field F] [Field L₁] [Field L₂] [Field M]
  [NumberField F] [NumberField L₁] [NumberField L₂] [NumberField M]
  [Algebra F L₁] [Algebra F L₂] [Algebra F M] [Algebra L₁ M] [Algebra L₂ M]
  [IsScalarTower F L₁ M] [IsScalarTower F L₂ M]
  [IsGalois F L₁] [IsGalois F L₂] [IsGalois F M]

/-- Representatives whose quotient classes agree in a common overfield have equal
total invariants, for place choices compatible with those in the common overfield. -/
theorem totalIdeleInvariant_eq_of_common_inflation
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (wf₁ : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L₁ v)
    (wf₂ : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L₂ v)
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove M v)
    (hf₁ : ∀ v, (wf v).1.asIdeal.LiesOver (wf₁ v).1.asIdeal)
    (hf₂ : ∀ v, (wf v).1.asIdeal.LiesOver (wf₂ v).1.asIdeal)
    (wi₁ : ∀ v : InfinitePlace F, InfinitePlacesAbove L₁ v)
    (wi₂ : ∀ v : InfinitePlace F, InfinitePlacesAbove L₂ v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove M v)
    (hi₁ : ∀ v, (wi v).1.comap (algebraMap L₁ M) = (wi₁ v).1)
    (hi₂ : ∀ v, (wi v).1.comap (algebraMap L₂ M) = (wi₂ v).1)
    (hrec : ∀ x : relativeCohomology F M 2, Reciprocity.SumOfInvariantsVanishes I x)
    (a : relativeIdeleCohomology F L₁ 2) (b : relativeIdeleCohomology F L₂ 2)
    (hab : relativeIdeleClassInflation F L₁ M 2 (ideleQuotientCohomologyMap F L₁ 2 a) =
      relativeIdeleClassInflation F L₂ M 2 (ideleQuotientCohomologyMap F L₂ 2 b)) :
    totalIdeleInvariant I hI wf₁ wi₁ a = totalIdeleInvariant I hI wf₂ wi₂ b := by
  rw [← totalIdeleInvariant_relativeIdeleInflation I hI hInf wf₁ wf hf₁ wi₁ wi hi₁,
    ← totalIdeleInvariant_relativeIdeleInflation I hI hInf wf₂ wf hf₂ wi₂ wi hi₂]
  apply totalIdeleInvariant_eq_of_quotient_eq I hI wf wi hrec
  calc
    ideleQuotientCohomologyMap F M 2 (relativeIdeleInflation F L₁ M 2 a) =
        relativeIdeleClassInflation F L₁ M 2 (ideleQuotientCohomologyMap F L₁ 2 a) :=
      ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F L₁ M 2) a
    _ = relativeIdeleClassInflation F L₂ M 2 (ideleQuotientCohomologyMap F L₂ 2 b) := hab
    _ = ideleQuotientCohomologyMap F M 2 (relativeIdeleInflation F L₂ M 2 b) :=
      (ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F L₂ M 2) b).symm

end CommonOverfield

end Langlands.ClassField.Global
