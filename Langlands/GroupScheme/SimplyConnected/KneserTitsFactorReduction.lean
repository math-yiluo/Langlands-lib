import Langlands.GroupScheme.SimplyConnected.KneserTitsFactorStatement
import Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement
import Langlands.GroupScheme.SimplyConnected.NormalFactors
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.RootGeneratedSubgroup
import Langlands.GroupScheme.Rational.ParabolicRadicalRootContainment
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Conditional assembly of the local Kneser–Tits factor inclusion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

/-- Local normal generation transfers along any group-scheme homomorphism
whose parabolic-radical images lie in the specified ambient normal subgroup. -/
theorem rationalPoints_range_le_of_localKneserTits
    (hKT : LocalKneserTitsStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom A.X.hom]
    (hA_sc : IsSimplyConnected A) (hA : IsAlmostSimple A)
    (hAi : ¬ IsAnisotropic A) (a : A ⟶ G)
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  let N := K.comap (rationalPoints.map a)
  have hN : N.Normal := inferInstance
  have hNtop : N = ⊤ := hKT F A hA_sc hA hAi N hN (by
    intro P U p r hp hr
    rintro _ ⟨x, rfl⟩
    change rationalPoints.map a (rationalPoints.map (r ≫ p) x) ∈ K
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
      using hrad P U p r hp hr ⟨x, rfl⟩)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N := by rw [hNtop]; trivial
  exact hx

/-- The actual rational-point homomorphism with codomain restricted using
the supplied local Kneser–Tits input and the parabolic-radical inclusions. -/
def rationalPointsToNormalSubgroupOfLocalKneserTits
    (hKT : LocalKneserTitsStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom A.X.hom]
    (hA_sc : IsSimplyConnected A) (hA : IsAlmostSimple A)
    (hAi : ¬ IsAnisotropic A) (a : A ⟶ G)
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) :
    rationalPoints A →* K :=
  (rationalPoints.map a).codRestrict K fun x =>
    rationalPoints_range_le_of_localKneserTits hKT hA_sc hA hAi a K hrad ⟨x, rfl⟩

/-- The factor conclusion follows from the arithmetic theorem, reflection
of simple connectedness to actual normal factors, and the listed structural
theorems. No retained input is asserted as proved here. -/
theorem simplyConnectedKneserTitsFactor_of_localKT_and_structural_inputs
    (hKT : LocalKneserTitsStatement.{u})
    (hcomp : SemisimpleNormalIsogenyComplementStatement.{u})
    (hBr : RationalBruhatStatement.{u})
    (hRankOne : RootRankOneFactorizationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    SimplyConnectedKneserTitsFactorStatement.{u} := by
  intro F _ _ _ _ G _ hG S i hi A a hA ha hn hAi
  have hGred := hG.isSemisimple.isConnectedReductive
  have hAred := hA.isSemisimple.isConnectedReductive
  let := hGred.smooth
  let := hAred.isAffineHom
  let := hi.isSplitSubtorus.mono
  have hRay := relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement
    hRankOne
  have hdisj := fun ν => (hRay F G hGred S i hi ν).2.1
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  let K := relativeRootGeneratedSubgroup i
  let : K.Normal :=
    relativeRootGeneratedSubgroup_normal_of_bruhat_of_disjoint_positive_rays
      i hGred hi ν hν (hBr F G hGred S i hi ν hν) (hdisj ν)
  exact rationalPoints_range_le_of_localKneserTits hKT
    (hG.normalSubgroup_of_normalIsogenyComplement hcomp a ha
      hAred.smooth hAred.connectedSpace hn) hA hAi a K
    (fun _ _ _ _ hp hr =>
      parabolicRadical_range_le_normalSubgroup_of_root_groups
        i hPD dynamicCentralizerReductive hconj hGred hi hdisj K
        (fun α hα => relativeRoot_subgroup_le_generated i hα)
        hAred a hp hr)

end Langlands.GroupScheme
