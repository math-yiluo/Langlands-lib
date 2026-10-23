import Langlands.ClassField.Global.IdeleTotalInvariant
import Langlands.Cohomology.Continuous.OrdinaryTransferLawsProof

/-! # The global degree bounds the denominator of the total idele invariant -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local
open CategoryTheory

universe u

/-- Degree-two group cohomology of a finite group is killed by the group order. -/
theorem card_nsmul_H2_eq_zero
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    (A : Rep.{u} k G) (c : groupCohomology A 2) :
    Nat.card G • c = 0 := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (⊥ : Subgroup G)
  let := Fintype.ofFinite (G ⧸ (⊥ : Subgroup G))
  have h := Langlands.Continuous.ordinaryCorestriction_index_pos (⊥ : Subgroup G) A 2
  have hz : Langlands.Tate.ordinaryCohomologyCorestriction (⊥ : Subgroup G) A 2 = 0 :=
    (isZero_groupCohomology_succ_of_subsingleton
      (Rep.res (⊥ : Subgroup G).subtype A) 1).eq_of_src _ _
  rw [hz, Limits.comp_zero, Subgroup.index_bot] at h
  exact (congrArg (fun f => f c) h).symm

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- Every total invariant is annihilated by the global extension degree. -/
theorem totalIdeleInvariant_mem_denominator
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    totalIdeleInvariant I hI wf wi c ∈ denominatorSubgroup (Module.finrank F E) := by
  change Module.finrank F E • totalIdeleInvariant I hI wf wi c = 0
  rw [← map_nsmul, ← IsGalois.card_aut_eq_finrank F E,
    card_nsmul_H2_eq_zero, map_zero]

/-- The total idele invariant with codomain the global degree denominator subgroup. -/
def totalIdeleInvariantToDenominator
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    relativeIdeleCohomology F E 2 →+ denominatorSubgroup (Module.finrank F E) :=
  (totalIdeleInvariant I hI wf wi).codRestrict _
    (totalIdeleInvariant_mem_denominator I hI wf wi)

@[simp] theorem totalIdeleInvariantToDenominator_coe
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    (totalIdeleInvariantToDenominator I hI wf wi c : RationalModIntegers) =
      totalIdeleInvariant I hI wf wi c :=
  rfl

/-- Reciprocity kills the quotient-map kernel also for the restricted codomain. -/
theorem totalIdeleInvariantToDenominator_eq_zero_of_ideleQuotient_eq_zero
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x)
    (c : relativeIdeleCohomology F E 2)
    (hc : ideleQuotientCohomologyMap F E 2 c = 0) :
    totalIdeleInvariantToDenominator I hI wf wi c = 0 :=
  Subtype.ext (totalIdeleInvariant_eq_zero_of_ideleQuotient_eq_zero I hI wf wi hrec c hc)

end Langlands.ClassField.Global
