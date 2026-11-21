import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.RankOneDeterminantBand
import Langlands.Global.Factors.CuspidalCommonSplitCentreTwist

/-! # Strong multiplicity one for cuspidal realizations of `GL₁` -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField Automorphic
open ContinuousRationalFunctions (evaluate)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)

/-- Strong multiplicity one for the rank-one case of the cuspidal statement. -/
def CuspidalStrongMultiplicityOneRankOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (T T' : CuspidalOperatorRealization F 0)
    (P : CuspidalSpectralPresentation.{u,uQ} T)
    (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)),
    (∀ v ∉ S, localClass P h v = localClass P' h' v) →
    T.isoClass = T'.isoClass

section RankOne

variable {F : Type u} [Field F] [NumberField F]

local instance : AddCommGroup (RationalInvariantFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F 1) := Submodule.addCommGroup _
local instance (T : OperatorRealization F 1) : AddCommGroup T.Space := Submodule.addCommGroup _

private def valueAtOne (T : OperatorRealization F 1) : T.Space →ₗ[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (1 : AdelicGL F 1)).toLinearMap.comp
    ((ContinuousRationalFunctions.toContinuousMap F 1).comp T.toContinuous)

private theorem vector_eq_of_valueAtOne_eq {T T' : OperatorRealization F 1}
    {ω : HeckeCharacter F} (hω : T.HasCentralCharacter ω) (hω' : T'.HasCentralCharacter ω)
    {f : T.Space} {f' : T'.Space} (h : valueAtOne T f = valueAtOne T' f') :
    f.val = f'.val := by
  apply stableAutomorphicInclusion_injective F 1
  apply automorphicToContinuous_injective F 1
  change T.toContinuous f = T'.toContinuous f'
  apply ContinuousRationalFunctions.toContinuousMap_injective F 1
  ext x
  let z := AdelicGL.determinant F 1 x
  rw [← AdelicGL.scalar_determinant_one F x]
  change evaluate F 1 (T.toContinuous f) (AdelicGL.scalar F 1 z) =
    evaluate F 1 (T'.toContinuous f') (AdelicGL.scalar F 1 z)
  rw [← mul_one (AdelicGL.scalar F 1 z), T.centralCharacter_evaluate ω hω f,
    T'.centralCharacter_evaluate ω hω' f']
  exact congrArg ((centralIdeleCharacter F ω z : ℂ) * ·) h

private theorem submodule_le_of_hasCentralCharacter [CompactSpace (AdeleQuotient F)]
    {T T' : CuspidalOperatorRealization F 0}
    {ω : HeckeCharacter F} (hω : T.HasCentralCharacter ω) (hω' : T'.HasCentralCharacter ω) :
    T.realization.toSubmodule ≤ T'.realization.toSubmodule := by
  obtain ⟨g, hg⟩ := exists_ne (0 : T'.Space)
  have hg₁ : valueAtOne T'.realization g ≠ 0 := by
    intro hz
    apply hg
    exact Subtype.ext (vector_eq_of_valueAtOne_eq hω' hω'
      (hz.trans ((valueAtOne T'.realization).map_zero).symm))
  intro f hf
  let x : T.Space := ⟨f, hf⟩
  let y : T'.Space := (valueAtOne T.realization x / valueAtOne T'.realization g) • g
  have hy : valueAtOne T.realization x = valueAtOne T'.realization y := by
    dsimp only [y]
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hg₁]
  have he := vector_eq_of_valueAtOne_eq hω hω' hy
  change f = y.val at he
  rw [he]
  exact y.property

end RankOne

/-- In rank one the common central character determines the full operator class. -/
theorem cuspidalStrongMultiplicityOneRankOne : CuspidalStrongMultiplicityOneRankOneStatement.{u,uQ} := by
  intro F _ _ _ T T' P P' h h' S hloc
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  have hω' := CuspidalCommonSplitCentreTwist.hasCentralCharacter_of_localClass_eq
    P P' h h' S hloc ω hω
  have he : T.realization = T'.realization := Subrepresentation.toSubmodule_injective
    (le_antisymm (submodule_le_of_hasCentralCharacter hω hω')
      (submodule_le_of_hasCentralCharacter hω' hω))
  apply CuspidalOperatorRealization.IsoClass.toOperatorClass_injective
  exact congrArg OperatorRealization.isoClass he

end Langlands.Global
