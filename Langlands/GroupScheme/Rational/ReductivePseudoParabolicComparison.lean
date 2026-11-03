import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyStatement
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.FppfProductTrivial

/-! # Conditional comparison of reductive parabolic and pseudo-parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}

/-- A parabolic has a product presentation with the identity subgroup, provided
the dynamic structure statement is supplied. -/
theorem IsParabolicSubgroup.exists_pseudoParabolicPresentation
    (hi : IsParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range (kernelUnit G)) i := by
  obtain ⟨χ, hχ⟩ := (hPD k G hG P i hi.isClosedSubgroup).mp hi
  refine ⟨χ, ?_⟩
  rw [range_kernelUnit, ← hχ]
  exact SubgroupFunctor.IsFppfProduct.range_bot i hi.isClosedSubgroup

/-- Choose a cocharacter and its all-test product presentation for an actual
parabolic. This supplies presentation data, not any structural input. -/
def IsParabolicSubgroup.pseudoParabolicPresentation
    (hi : IsParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) :
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G //
      (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range (kernelUnit G)) i} :=
  Classical.indefiniteDescription _ (hi.exists_pseudoParabolicPresentation hPD hG)

/-- Under the supplied structure theorem and ground-field radical triviality,
every parabolic is pseudo-parabolic as an actual subgroup scheme. -/
theorem IsParabolicSubgroup.isPseudoParabolicSubgroup_of_parabolicDynamic
    (hi : IsParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (hR : HasTrivialUnipotentRadical G) :
    IsPseudoParabolicSubgroup i := by
  have := hG.isAffineHom
  obtain ⟨χ, hχ⟩ := hi.exists_pseudoParabolicPresentation hPD hG
  exact ⟨hG.smooth, hG.connectedSpace, hG.isAffineHom,
    Grp.trivial _, kernelUnit G, χ, isUnipotentRadical_kernelUnit G hR, hχ⟩

/-- In the same setting, every pseudo-parabolic is parabolic. The comparison
uses all relative tests and a represented dynamic parabolic. -/
theorem IsPseudoParabolicSubgroup.isParabolicSubgroup_of_parabolicDynamic
    (hi : IsPseudoParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (hR : HasTrivialUnipotentRadical G) :
    IsParabolicSubgroup i := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  apply (hPD k G hG P i hi.isClosedSubgroup).mpr
  exact ⟨χ, hprod.range_eq_left_of_right_eq_bot
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ) (hj.range_eq_bot hR)⟩

/-- Conditional equality of the two actual-subgroup notions for a connected
reductive group, with ground-field radical triviality still explicit. -/
theorem isParabolicSubgroup_iff_isPseudoParabolicSubgroup_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (hR : HasTrivialUnipotentRadical G) :
    IsParabolicSubgroup i ↔ IsPseudoParabolicSubgroup i :=
  ⟨fun hi => hi.isPseudoParabolicSubgroup_of_parabolicDynamic hPD hG hR,
    fun hi => hi.isParabolicSubgroup_of_parabolicDynamic hPD hG hR⟩

/-- All-test minimality transfers from parabolic to pseudo-parabolic subgroups. -/
theorem IsMinimalParabolicSubgroup.isMinimalPseudoParabolicSubgroup_of_parabolicDynamic
    (hi : IsMinimalParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (hR : HasTrivialUnipotentRadical G) :
    IsMinimalPseudoParabolicSubgroup i := by
  refine ⟨hi.1.isPseudoParabolicSubgroup_of_parabolicDynamic hPD hG hR, ?_⟩
  intro Q j hj hle
  exact hi.2 Q j (hj.isParabolicSubgroup_of_parabolicDynamic hPD hG hR) hle

/-- All-test minimality transfers from pseudo-parabolic to parabolic subgroups. -/
theorem IsMinimalPseudoParabolicSubgroup.isMinimalParabolicSubgroup_of_parabolicDynamic
    (hi : IsMinimalPseudoParabolicSubgroup i) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G) (hR : HasTrivialUnipotentRadical G) :
    IsMinimalParabolicSubgroup i := by
  refine ⟨hi.1.isParabolicSubgroup_of_parabolicDynamic hPD hG hR, ?_⟩
  intro Q j hj hle
  exact hi.2 Q j (hj.isPseudoParabolicSubgroup_of_parabolicDynamic hPD hG hR) hle

/-- Conditional equality of the minimal subgroup notions, using the original
all-test range inclusion and equality without any change of representative. -/
theorem isMinimalParabolicSubgroup_iff_isMinimalPseudoParabolicSubgroup_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (hR : HasTrivialUnipotentRadical G) :
    IsMinimalParabolicSubgroup i ↔ IsMinimalPseudoParabolicSubgroup i :=
  ⟨fun hi => hi.isMinimalPseudoParabolicSubgroup_of_parabolicDynamic hPD hG hR,
    fun hi => hi.isMinimalParabolicSubgroup_of_parabolicDynamic hPD hG hR⟩

/-- The pseudo-parabolic route to the exact minimal-parabolic conjugacy
statement. All three missing structural inputs remain explicit. -/
theorem minimalParabolicConjugacyStatement_of_pseudoParabolic
    (hPD : ParabolicDynamicStatement.{u})
    (hR : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → HasTrivialUnipotentRadical G)
    (hconj : MinimalPseudoParabolicConjugacyStatement.{u}) :
    MinimalParabolicConjugacyStatement.{u} := by
  intro k _ G hG P P' j j' hj hj'
  exact hconj k G hG.smooth hG.connectedSpace hG.isAffineHom P P' j j'
    (hj.isMinimalPseudoParabolicSubgroup_of_parabolicDynamic hPD hG (hR k G hG))
    (hj'.isMinimalPseudoParabolicSubgroup_of_parabolicDynamic hPD hG (hR k G hG))

end Langlands.GroupScheme
