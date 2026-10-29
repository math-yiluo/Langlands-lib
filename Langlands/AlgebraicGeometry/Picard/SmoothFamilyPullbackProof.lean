import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPullbackStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackComparison
import Langlands.AbelianScheme.FibreComparison

/-! # Pullback preservation of actual smooth-family witnesses -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A B : AbelianScheme S)

/-- Keep the parameter fixed and map the abelian-scheme factor. -/
private def smoothFamilyProductMap (f : A.X ⟶ B.X) (C : Over S) :
    (relativeSpace A.X.hom).obj C ⟶ (relativeSpace B.X.hom).obj C :=
  pullback.lift (pullback.fst C.hom A.X.hom)
    (pullback.snd C.hom A.X.hom ≫ f.left)
    (by rw [Category.assoc, f.w]; exact pullback.condition)

/-- The map on products commutes with restriction at each marked point. -/
private lemma smoothFamilyPointMap_productMap (f : A.X ⟶ B.X) (C : Over S)
    (c : Over.mk (𝟙 S) ⟶ C) :
    smoothFamilyPointMap A C c ≫ smoothFamilyProductMap A B f C =
      f.left ≫ smoothFamilyPointMap B C c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothFamilyProductMap, pullback.lift_fst,
      smoothFamilyPointMap_fst]
    rw [← Category.assoc, f.w]
  · rw [Category.assoc, smoothFamilyProductMap, pullback.lift_snd,
      ← Category.assoc, smoothFamilyPointMap_snd, Category.id_comp,
      Category.assoc, smoothFamilyPointMap_snd, Category.comp_id]

/-- Pulling back a witness commutes with its endpoint restrictions. -/
private def smoothFamilyEndpointPullbackIso (f : A.X ⟶ B.X) (C : Over S)
    (c : Over.mk (𝟙 S) ⟶ C)
    (N : LineBundle ((relativeSpace B.X.hom).obj C)) :
    (LineBundle.pullback (smoothFamilyPointMap A C c)).obj
        ((LineBundle.pullback (smoothFamilyProductMap A B f C)).obj N) ≅
      (LineBundle.pullback f.left).obj
        ((LineBundle.pullback (smoothFamilyPointMap B C c)).obj N) :=
  (LineBundle.pullbackComp _ _).app N ≪≫
    eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj N)
      (smoothFamilyPointMap_productMap A B f C c)) ≪≫
    ((LineBundle.pullbackComp _ _).app N).symm

/-- The same parameter and marked points witness triviality after pullback. -/
private lemma smoothFamilyTriviality_pullback
    {K : Type u} [Field K] [IsAlgClosed K]
    (A B : AbelianScheme (Spec (CommRingCat.of K))) (f : A.X ⟶ B.X)
    {L : LineBundle B.X.left}
    (hL : IsAlgebraicallyTrivialViaSmoothFamily B L) :
    IsAlgebraicallyTrivialViaSmoothFamily A ((LineBundle.pullback f.left).obj L) := by
  obtain ⟨C, hSm, hSep, hFt, hQc, hInt, c0, c1, N, ⟨e0⟩, ⟨e1⟩⟩ := hL
  refine ⟨C, hSm, hSep, hFt, hQc, hInt, c0, c1,
    (LineBundle.pullback (smoothFamilyProductMap A B f C)).obj N, ⟨?_⟩, ⟨?_⟩⟩
  · exact smoothFamilyEndpointPullbackIso A B f C c0 N ≪≫
      (LineBundle.pullback f.left).mapIso e0 ≪≫ LineBundle.pullbackTrivialIso f.left
  · exact smoothFamilyEndpointPullbackIso A B f C c1 N ≪≫
      (LineBundle.pullback f.left).mapIso e1

set_option maxHeartbeats 800000 in
/-- Actual relative rigidified pullback preserves smooth-family algebraic triviality. -/
theorem smoothFamilyPullback : SmoothFamilyPullbackStatement.{u} := by
  intro S A T U h L hL K _ _ s
  let m := GroupScheme.fibreComparison A.toGrp h s
  have hp := smoothFamilyTriviality_pullback
    ((baseChange s).obj ((baseChange T.hom).obj A))
    ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A))
    m.hom.hom (hL K (s ≫ h.left))
  exact isAlgebraicallyTrivialViaSmoothFamily_of_iso
    ((baseChange s).obj ((baseChange T.hom).obj A))
    (fibreComparison_lineBundleIso A h s m
      (GroupScheme.fibreComparison_fst A.toGrp h s) L)
    hp

end Langlands.AbelianScheme
