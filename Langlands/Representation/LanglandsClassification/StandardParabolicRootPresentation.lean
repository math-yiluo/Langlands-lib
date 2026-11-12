import Langlands.Representation.LanglandsClassification.StandardParabolicDatum
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof

/-! # Verified root presentations for the canonical standard data

The presentation retains the fixed maximal split torus, generic cocharacter,
simple-root subset and the supplied actual split-component factor. Every
compatibility clause is proved for the original standard schemes and maps.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.ParabolicDatum

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (a : A.toGrp ⟶ Standard.leviScheme i ν J) (ha : IsSplitComponent a)
  (g : A.toGrp ⟶ T.toGrp) (hg : g ≫ i = a ≫ Standard.leviHom i ν J)

/-- The original standard datum and a supplied actual split-component factor
have a verified root presentation with precisely the fixed choices. -/
def standardRootPresentation :
    ParabolicRootPresentation
      (standard i ν hG hi hν J hJ).p (standard i ν hG hi hν J hJ).l a := by
  refine ⟨⟨T, i, ν, J, Additive.ofMul g⟩, ?_⟩
  have := hi.isSplitSubtorus.mono
  let D := standard i ν hG hi hν J hJ
  have hP := range_standard_p i ν hG hi hν J hJ
  have hL := range_standard_l_comp_p i ν hG hi hν J hJ
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  refine
    { parabolic := D.hp
      levi := D.hl
      splitComponent := ha
      maximalSplit := hi
      generic := hν
      subset_simpleRoots := hJ
      parabolic_eq := hP
      levi_eq := hL
      factor_comp := ?_
      minimal := genericMinimalParabolic k G hG T i hi ν hν
      minimal_le := ?_
      realization := ⟨ζ, hζ, hP.trans (hcompare ζ hζ).1,
        hL.trans (hcompare ζ hζ).2.1⟩ }
  · change g ≫ i =
      a ≫ Standard.leviToParabolic i ν J ≫ Standard.parabolicHom i ν J
    rw [Standard.leviToParabolic_comp]
    exact hg
  · change Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      SubgroupFunctor.range D.p
    rw [hP, ← (standardParabolicEndpoints k G hG T i hi ν hν).1]
    exact ((standardParabolicOrder k G hG T i hi ν hν).1
      ∅ J (Set.empty_subset _) hJ).1.mp (Set.empty_subset _)

/-- The verified presentation keeps the original torus, cocharacter, subset
and actual split-component factor, with no conjugation or replacement. -/
@[simp] theorem standardRootPresentation_data :
    (standardRootPresentation i ν hG hi hν J hJ a ha g hg).data =
      ⟨T, i, ν, J, Additive.ofMul g⟩ := rfl

end Langlands.Aubert.General.RepresentedParabolic.ParabolicDatum
