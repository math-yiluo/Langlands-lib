import Langlands.ClassField.Global.IdeleInvariantDenominator
import Langlands.ClassField.Global.IdeleTotalSection
import Langlands.ClassFieldTheory.Local.UnramifiedInvariant
import Langlands.GroupTheory.FiniteInvariantDescent

/-! # Conditional descent of the total invariant to idele-class cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
  (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

/-- A selected finite place of full local degree makes the total invariant onto. -/
theorem totalIdeleInvariantToDenominator_surjective_of_fullLocalDegree
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (hdegree : Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E) =
      Module.finrank F E) :
    Function.Surjective (totalIdeleInvariantToDenominator I hI wf wi) := by
  intro y
  let y' : denominatorSubgroup
      (Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E)) :=
    ⟨y, by rw [hdegree]; exact y.property⟩
  refine ⟨finiteIdeleInvariantLift I hI v (wf v).1 y', ?_⟩
  apply Subtype.ext
  exact totalIdeleInvariant_finiteIdeleInvariantLift I hI wf wi v y'

private theorem quotient_ker_le_total_ker
    (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x) :
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom.ker ≤
      (totalIdeleInvariantToDenominator I hI wf wi).ker := by
  intro c hc
  exact totalIdeleInvariantToDenominator_eq_zero_of_ideleQuotient_eq_zero
    I hI wf wi hrec c hc

private theorem denominator_natCard (n : ℕ) (hn : 0 < n) :
    Nat.card (denominatorSubgroup n) = n :=
  (Nat.card_congr (denominatorEquiv n hn).toEquiv).symm.trans (Nat.card_zmod n)

variable (v : HeightOneSpectrum (𝓞 F))
  [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
  (hdegree : Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E) =
    Module.finrank F E)
  (hrec : ∀ x : relativeCohomology F E 2, Reciprocity.SumOfInvariantsVanishes I x)
  [Finite (relativeIdeleClassCohomology F E 2)]
  (hcard : Nat.card (relativeIdeleClassCohomology F E 2) ≤ Module.finrank F E)

/-- Under reciprocity, a cardinality bound and a finite place of full local degree,
the total invariant descends to an equivalence on actual idele-class cohomology. -/
def ideleClassInvariantEquivOfFullLocalDegree :
    relativeIdeleClassCohomology F E 2 ≃+ denominatorSubgroup (Module.finrank F E) :=
  Langlands.FiniteInvariantDescent.equiv
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom
    (totalIdeleInvariantToDenominator I hI wf wi)
    (quotient_ker_le_total_ker I hI wf wi hrec)
    (totalIdeleInvariantToDenominator_surjective_of_fullLocalDegree I hI wf wi v hdegree)
    (by rwa [denominator_natCard _ (Module.finrank_pos : 0 < Module.finrank F E)])

/-- The equivalence agrees with the total invariant before the quotient cohomology map. -/
@[simp] theorem ideleClassInvariantEquivOfFullLocalDegree_apply_quotient
    (c : relativeIdeleCohomology F E 2) :
    ideleClassInvariantEquivOfFullLocalDegree I hI wf wi v hdegree hrec hcard
      (ideleQuotientCohomologyMap F E 2 c) =
        totalIdeleInvariantToDenominator I hI wf wi c := by
  exact Langlands.FiniteInvariantDescent.equiv_apply _ _ _ _ _ c

include I hI wf wi v hdegree hrec hcard in
/-- The same hypotheses force the actual quotient cohomology map onto. -/
theorem ideleQuotientCohomologyMap_surjective_of_fullLocalDegree :
    Function.Surjective (ideleQuotientCohomologyMap F E 2) :=
  Langlands.FiniteInvariantDescent.surjective_of_card_le
    (ideleQuotientCohomologyMap F E 2).hom.toAddMonoidHom
    (totalIdeleInvariantToDenominator I hI wf wi)
    (quotient_ker_le_total_ker I hI wf wi hrec)
    (totalIdeleInvariantToDenominator_surjective_of_fullLocalDegree I hI wf wi v hdegree)
    (by rwa [denominator_natCard _ (Module.finrank_pos : 0 < Module.finrank F E)])

/-- The conditional invariant with values in the rational numbers modulo integers. -/
def ideleClassInvariantOfFullLocalDegree :
    relativeIdeleClassCohomology F E 2 →+ RationalModIntegers :=
  (denominatorSubgroup (Module.finrank F E)).subtype.comp
    (ideleClassInvariantEquivOfFullLocalDegree I hI wf wi v hdegree hrec hcard).toAddMonoidHom

theorem ideleClassInvariantOfFullLocalDegree_injective :
    Function.Injective (ideleClassInvariantOfFullLocalDegree I hI wf wi v hdegree hrec hcard) :=
  Subtype.val_injective.comp
    (ideleClassInvariantEquivOfFullLocalDegree I hI wf wi v hdegree hrec hcard).injective

theorem ideleClassInvariantOfFullLocalDegree_range :
    (ideleClassInvariantOfFullLocalDegree I hI wf wi v hdegree hrec hcard).range =
      denominatorSubgroup (Module.finrank F E) := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact (ideleClassInvariantEquivOfFullLocalDegree I hI wf wi v hdegree hrec hcard c).property
  · intro hy
    obtain ⟨c, hc⟩ :=
      (ideleClassInvariantEquivOfFullLocalDegree I hI wf wi v hdegree hrec hcard).surjective ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩

@[simp] theorem ideleClassInvariantOfFullLocalDegree_apply_quotient
    (c : relativeIdeleCohomology F E 2) :
    ideleClassInvariantOfFullLocalDegree I hI wf wi v hdegree hrec hcard
      (ideleQuotientCohomologyMap F E 2 c) = totalIdeleInvariant I hI wf wi c := by
  exact congrArg Subtype.val
    (ideleClassInvariantEquivOfFullLocalDegree_apply_quotient I hI wf wi v hdegree hrec hcard c)

end Langlands.ClassField.Global
