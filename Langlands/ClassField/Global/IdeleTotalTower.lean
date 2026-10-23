import Langlands.ClassField.Global.IdeleArchimedeanTower
import Langlands.ClassField.Global.IdeleFiniteTower
import Langlands.ClassField.Global.IdeleTotalInvariant
import Langlands.GroupTheory.FiniteInvariantDescent

/-! # Total idele invariants under inflation -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.ClassFieldTheory.Local CategoryTheory
open Langlands.Global.AdelicFunctoriality

universe u

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]

/-- Inflation preserves the total idele invariant at compatible finite and infinite places. -/
theorem totalIdeleInvariant_relativeIdeleInflation
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
    (hf : ∀ v, (wf' v).1.asIdeal.LiesOver (wf v).1.asIdeal)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
    (hi : ∀ v, (wi' v).1.comap (algebraMap E L) = (wi v).1)
    (x : relativeIdeleCohomology F E 2) :
    totalIdeleInvariant I hI wf' wi' (relativeIdeleInflation F E L 2 x) =
      totalIdeleInvariant I hI wf wi x := by
  change finiteIdeleInvariantSum I hI wf' (relativeIdeleInflation F E L 2 x) +
      archimedeanIdeleInvariantSum wi' (relativeIdeleInflation F E L 2 x) =
    finiteIdeleInvariantSum I hI wf x + archimedeanIdeleInvariantSum wi x
  rw [finiteIdeleInvariantSum_relativeIdeleInflation I hI hInf wf wf' hf,
    archimedeanIdeleInvariantSum_relativeIdeleInflation wi wi' hi]


/-- Inflation on the subgroup of idele-class cohomology represented by idele classes. -/
def ideleQuotientRangeInflation :
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.range →+
      (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.range where
  toFun c := ⟨relativeIdeleClassInflation F E L 2 c,
    relativeIdeleClassInflation_mem_quotient_range F E L 2 c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext ((relativeIdeleClassInflation F E L 2).hom.map_add c.val d.val)

omit [NumberField F] [IsGalois F L] in
/-- On a represented class, range inflation is induced by actual idele inflation. -/
theorem ideleQuotientRangeInflation_apply_quotient (a : relativeIdeleCohomology F E 2) :
    ideleQuotientRangeInflation
        ((ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.rangeRestrict a) =
      (ideleQuotientCohomologyMap F L 2).hom.toAddMonoidHom.rangeRestrict
        (relativeIdeleInflation F E L 2 a) := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom (relativeIdeleInflation_comp_quotient F E L 2) a).symm

section RangeInvariant

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
  (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
  (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x)

/-- Under reciprocity the total invariant descends to the quotient-map range. -/
def ideleClassInvariantOnQuotientRange :
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.range →+ RationalModIntegers :=
  Langlands.FiniteInvariantDescent.onRange
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom (totalIdeleInvariant I hI wf wi)
    (fun c hc => totalIdeleInvariant_eq_zero_of_ideleQuotient_eq_zero I hI wf wi hrec c hc)

@[simp] theorem ideleClassInvariantOnQuotientRange_apply_quotient
    (a : relativeIdeleCohomology F E 2) :
    ideleClassInvariantOnQuotientRange I hI wf wi hrec
        ((ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.rangeRestrict a) =
      totalIdeleInvariant I hI wf wi a :=
  Langlands.FiniteInvariantDescent.onRange_apply _ _ _ a

include hrec in
/-- Equal images under the quotient map have equal total invariants, under reciprocity. -/
theorem totalIdeleInvariant_eq_of_quotient_eq
    {a b : relativeIdeleCohomology F E 2}
    (hab : ideleQuotientCohomologyMap F E 2 a = ideleQuotientCohomologyMap F E 2 b) :
    totalIdeleInvariant I hI wf wi a = totalIdeleInvariant I hI wf wi b := by
  rw [← ideleClassInvariantOnQuotientRange_apply_quotient I hI wf wi hrec,
    ← ideleClassInvariantOnQuotientRange_apply_quotient I hI wf wi hrec]
  exact congrArg (ideleClassInvariantOnQuotientRange I hI wf wi hrec) (Subtype.ext hab)

/-- The descended invariants on the quotient-map ranges commute with inflation. -/
theorem ideleClassInvariantOnQuotientRange_inflation
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
    (hf : ∀ v, (wf' v).1.asIdeal.LiesOver (wf v).1.asIdeal)
    (wi' : ∀ v : InfinitePlace F, InfinitePlacesAbove L v)
    (hi : ∀ v, (wi' v).1.comap (algebraMap E L) = (wi v).1)
    (hrec' : ∀ x : relativeCohomology F L 2, Reciprocity.SumOfInvariantsVanishes I x)
    (c : (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.range) :
    ideleClassInvariantOnQuotientRange I hI wf' wi' hrec'
        (ideleQuotientRangeInflation c) =
      ideleClassInvariantOnQuotientRange I hI wf wi hrec c := by
  obtain ⟨a, rfl⟩ := (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.rangeRestrict_surjective c
  rw [ideleQuotientRangeInflation_apply_quotient,
    ideleClassInvariantOnQuotientRange_apply_quotient,
    ideleClassInvariantOnQuotientRange_apply_quotient,
    totalIdeleInvariant_relativeIdeleInflation I hI hInf wf wf' hf wi wi' hi]

end RangeInvariant

end Langlands.ClassField.Global
