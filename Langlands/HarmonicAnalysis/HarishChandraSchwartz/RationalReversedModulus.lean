import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # The exact modulus cancellation after reversing the minimal parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

private theorem closedRestrictCharacter_same_element
    {H : Type*} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [IsTopologicalGroup H] (U : Subgroup H) (hU : IsClosed (U : Set H))
    {M M' : Subgroup H} (hM : M ≤ Subgroup.normalizer (U : Set H))
    (hM' : M' ≤ Subgroup.normalizer (U : Set H)) {m : M} {m' : M'}
    (hm : (m : H) = m') :
    HaarModulus.closedRestrictCharacter U hU M hM m =
      HaarModulus.closedRestrictCharacter U hU M' hM' m' := by
  simp only [HaarModulus.closedRestrictCharacter, MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext hm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

/-- The actual radical moduli for the original and reversed standard data are
reciprocal at the same ambient point of the common Levi. -/
theorem standardUnipotentModulus_mul_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (m : standardLeviPoints i ν J)
    (n : standardLeviPoints i (-ν) (Neg.neg '' J))
    (hmn : (m : rationalPoints G) = n) :
    standardUnipotentModulus i ν J m *
      standardUnipotentModulus i (-ν) (Neg.neg '' J) n = 1 := by
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨-, hM, hU⟩ := hcompare ζ hζ
  obtain ⟨-, hL, hO⟩ := standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν
    (relativeRootNegation F G hG S i hi) hζ
  have hL' : standardLeviPoints i (-ν) (Neg.neg '' J) = standardLeviPoints i ν J :=
    congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hL
  have hMO : standardLeviPoints i ν J ≤ Subgroup.normalizer
      (standardUnipotentPoints i (-ν) (Neg.neg '' J) : Set (rationalPoints G)) := by
    rw [← hL']
    exact standardLeviPoints_le_normalizer_standardUnipotentPoints i (-ν) (Neg.neg '' J)
  have hrec := dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
    centralSplitTorusCharacter hG
    (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i))
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardUnipotentPoints i (-ν) (Neg.neg '' J))
    (by rw [Dynamic.inverseCocharacter_inverseCocharacter];
        exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hU)
    (by rw [Dynamic.centralizer_inverseCocharacter];
        exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hM)
    (congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _))) hO)
    (isClosed_standardUnipotentPoints i ν J)
    (isClosed_standardUnipotentPoints i (-ν) (Neg.neg '' J))
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) hMO m
  have hchar := closedRestrictCharacter_same_element
    (standardUnipotentPoints i (-ν) (Neg.neg '' J))
    (isClosed_standardUnipotentPoints i (-ν) (Neg.neg '' J)) hMO
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i (-ν) (Neg.neg '' J)) hmn
  change standardUnipotentModulus i ν J m * _ = 1 at hrec
  rw [hchar] at hrec
  exact hrec

/-- Multiplication by the original radical modulus cancels its reversed
counterpart in the reversed minimal-modulus factorization. -/
theorem rationalMinimalModulus_reversed_mul (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (m : standardLeviPoints i ν J)
    (p : (standardParabolicPoints i (-ν) ∅).subgroupOf
      (standardLeviPoints i (-ν) (Neg.neg '' J)))
    (hmp : (m : rationalPoints G) = (p : standardLeviPoints i (-ν) (Neg.neg '' J))) :
    rationalMinimalModulus i (-ν) ⟨(p : standardLeviPoints i (-ν) (Neg.neg '' J)), p.2⟩ *
      standardUnipotentModulus i ν J m =
        standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J) p := by
  have hJ' : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rintro _ ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν (relativeRootNegation F G hG S i hi) (hJ hα)
  have hfact := rationalMinimalModulus_eq_mul hG hi (hν.neg i ν) hJ'
    ⟨(p : standardLeviPoints i (-ν) (Neg.neg '' J)), ⟨p.2, (p : standardLeviPoints i (-ν) (Neg.neg '' J)).2⟩⟩
  have hrec := standardUnipotentModulus_mul_reversed hG hi hν hJ m
    (p : standardLeviPoints i (-ν) (Neg.neg '' J)) hmp
  rw [hfact, standardLeviMinimalModulusOf_apply, mul_assoc, mul_comm
    (standardUnipotentModulus i (-ν) (Neg.neg '' J) _), hrec, mul_one]

/-- Exact radical reciprocity and reversed minimal-modulus cancellation on actual points. -/
def RationalReversedModulusStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
      (∀ (m : standardLeviPoints i ν J)
        (n : standardLeviPoints i (-ν) (Neg.neg '' J)), (m : rationalPoints G) = n →
        standardUnipotentModulus i ν J m *
          standardUnipotentModulus i (-ν) (Neg.neg '' J) n = 1) ∧
      (∀ (m : standardLeviPoints i ν J)
        (p : (standardParabolicPoints i (-ν) ∅).subgroupOf
          (standardLeviPoints i (-ν) (Neg.neg '' J))),
        (m : rationalPoints G) = (p : standardLeviPoints i (-ν) (Neg.neg '' J)) →
        rationalMinimalModulus i (-ν) ⟨(p : standardLeviPoints i (-ν) (Neg.neg '' J)), p.2⟩ *
          standardUnipotentModulus i ν J m =
            standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J) p)

/-- The exact modulus cancellation needed for the opposite-parabolic orientation. -/
theorem rationalReversedModulus : RationalReversedModulusStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ
  exact ⟨standardUnipotentModulus_mul_reversed hG hi hν hJ,
    rationalMinimalModulus_reversed_mul hG hi hν hJ⟩

end Langlands.HarishChandraSchwartz
