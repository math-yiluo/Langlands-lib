import Langlands.AlgebraicGeometry.Picard.CubeRelativeTransport
import Langlands.AlgebraicGeometry.Picard.CubeIsomorphismAssembly
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # Rigidified class comparison from ordinary relative cube triviality -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace CubeRelativeTransport

variable {S : Scheme.{u}} (X Y Z : Over S)
  (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
  (z₀ : Over.mk (𝟙 S) ⟶ Z)

/-- The first face becomes the relative section after inverse transport. -/
lemma cubeFirst_inv_prodIso :
    (CubeFace.first X Y Z x₀).left ≫ (relativeSpaceProdIso X (Y ⨯ Z)).inv =
      (relativeSection X.hom x₀.left (overSection_comp X x₀)).app (Y ⨯ Z) := by
  rw [← relativeSection_cubeFirst X Y Z x₀]
  simp

/-- The second face becomes the relative pullback along the second axis. -/
lemma cubeSecond_inv_prodIso :
    (CubeFace.second X Y Z y₀).left ≫ (relativeSpaceProdIso X (Y ⨯ Z)).inv =
      (relativeSpaceProdIso X Z).inv ≫
        (relativeSpace X.hom).map (CubeFace.secondAxis Y Z y₀) := by
  calc
    _ = (relativeSpaceProdIso X Z).inv ≫
        ((relativeSpaceProdIso X Z).hom ≫ (CubeFace.second X Y Z y₀).left) ≫
          (relativeSpaceProdIso X (Y ⨯ Z)).inv := by simp
    _ = (relativeSpaceProdIso X Z).inv ≫
        ((relativeSpace X.hom).map (CubeFace.secondAxis Y Z y₀) ≫
          (relativeSpaceProdIso X (Y ⨯ Z)).hom) ≫
            (relativeSpaceProdIso X (Y ⨯ Z)).inv := by
      rw [← relativeSpaceProdIso_cubeSecond X Y Z y₀]
    _ = _ := by simp

/-- The third face becomes the relative pullback along the third axis. -/
lemma cubeThird_inv_prodIso :
    (CubeFace.third X Y Z z₀).left ≫ (relativeSpaceProdIso X (Y ⨯ Z)).inv =
      (relativeSpaceProdIso X Y).inv ≫
        (relativeSpace X.hom).map (CubeFace.thirdAxis Y Z z₀) := by
  calc
    _ = (relativeSpaceProdIso X Y).inv ≫
        ((relativeSpaceProdIso X Y).hom ≫ (CubeFace.third X Y Z z₀).left) ≫
          (relativeSpaceProdIso X (Y ⨯ Z)).inv := by simp
    _ = (relativeSpaceProdIso X Y).inv ≫
        ((relativeSpace X.hom).map (CubeFace.thirdAxis Y Z z₀) ≫
          (relativeSpaceProdIso X (Y ⨯ Z)).hom) ≫
            (relativeSpaceProdIso X (Y ⨯ Z)).inv := by
      rw [← relativeSpaceProdIso_cubeThird X Y Z z₀]
    _ = _ := by simp

/-- An ordinary three-face cube triviality criterion applies to the actual
relative space after transporting its section and two axis restrictions. -/
def relativeTrivializationOfCubeTriviality
    (triviality : ∀ D : LineBundle (X ⨯ (Y ⨯ Z)).left,
      Nonempty ((Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj D.obj ≅
        structureSheaf (Y ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj D.obj ≅
        structureSheaf (X ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj D.obj ≅
        structureSheaf (X ⨯ Y).left) →
      Nonempty (D.obj ≅ structureSheaf (X ⨯ (Y ⨯ Z)).left))
    (D : LineBundle ((relativeSpace X.hom).obj (Y ⨯ Z)))
    (τ₁ : (Scheme.Modules.pullback
      ((relativeSection X.hom x₀.left (overSection_comp X x₀)).app (Y ⨯ Z))).obj
        D.obj ≅ structureSheaf (Y ⨯ Z).left)
    (τ₂ : (Scheme.Modules.pullback
      ((relativeSpace X.hom).map (CubeFace.secondAxis Y Z y₀))).obj D.obj ≅
        structureSheaf ((relativeSpace X.hom).obj Z))
    (τ₃ : (Scheme.Modules.pullback
      ((relativeSpace X.hom).map (CubeFace.thirdAxis Y Z z₀))).obj D.obj ≅
        structureSheaf ((relativeSpace X.hom).obj Y)) :
    D.obj ≅ structureSheaf ((relativeSpace X.hom).obj (Y ⨯ Z)) := by
  let E := (LineBundle.pullback (relativeSpaceProdIso X (Y ⨯ Z)).inv).obj D
  let e₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj E.obj ≅
      structureSheaf (Y ⨯ Z).left :=
    (Scheme.Modules.pullbackComp _ _).app D.obj ≪≫
      (Scheme.Modules.pullbackCongr (cubeFirst_inv_prodIso X Y Z x₀)).app D.obj ≪≫ τ₁
  let e₂ : (Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj E.obj ≅
      structureSheaf (X ⨯ Z).left :=
    pullbackSquareTrivialization _ _ _ _ (cubeSecond_inv_prodIso X Y Z y₀) D.obj τ₂
  let e₃ : (Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj E.obj ≅
      structureSheaf (X ⨯ Y).left :=
    pullbackSquareTrivialization _ _ _ _ (cubeThird_inv_prodIso X Y Z z₀) D.obj τ₃
  exact recoverTrivialization (relativeSpaceProdIso X (Y ⨯ Z)).symm D.obj
    (Classical.choice (triviality E ⟨e₁⟩ ⟨e₂⟩ ⟨e₃⟩))

end CubeRelativeTransport

namespace RigidifiedLineBundle

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include preservation in
/-- A section and two relative restrictions detect equality of rigidified
classes whenever ordinary line-bundle triviality is detected by those maps. -/
lemma classes_eq_of_threePullbackTriviality {T U V : Over S}
    (h : U ⟶ T) (k : V ⟶ T)
    (comparison : LocallyFreeRankOneIffTensorInvertibleStatement ((relativeSpace f).obj T))
    (triviality : ∀ D : LineBundle ((relativeSpace f).obj T),
      Nonempty ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj
        D.obj ≅ structureSheaf T.left) →
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map h)).obj D.obj ≅
        structureSheaf ((relativeSpace f).obj U)) →
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map k)).obj D.obj ≅
        structureSheaf ((relativeSpace f).obj V)) →
      Nonempty (D.obj ≅ structureSheaf ((relativeSpace f).obj T)))
    (q r : Classes f ε section_eq T)
    (hh : classesPullback f ε section_eq h q = classesPullback f ε section_eq h r)
    (hk : classesPullback f ε section_eq k q = classesPullback f ε section_eq k r) :
    q = r := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      obtain ⟨e₂⟩ := Quotient.exact hh
      obtain ⟨e₃⟩ := Quotient.exact hk
      let e := lineBundleIsoOfThreePullbackComparisons comparison preservation
        ((relativeSection f ε section_eq).app T)
        ((relativeSpace f).map h) ((relativeSpace f).map k) triviality
        ((forget _).obj L) ((forget _).obj M)
        (L.obj.rigidification.symm ≪≫ M.obj.rigidification)
        (((forget _ ⋙ LineBundle.forget _).mapIso e₂))
        (((forget _ ⋙ LineBundle.forget _).mapIso e₃))
      exact Quotient.sound ⟨isoOfCarrierIso preservation ((relativeProjection f).app T)
        (relativeSection_projection f ε section_eq T) e⟩

end RigidifiedLineBundle

/-- Ordinary cube triviality implies two-axis equality detection for the actual
relative rigidified classes, with tensor comparison hypotheses explicit. -/
lemma rigidifiedClasses_eq_of_cubeTriviality
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (X Y Z : Over S)
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
    (z₀ : Over.mk (𝟙 S) ⟶ Z)
    (comparison : LocallyFreeRankOneIffTensorInvertibleStatement
      ((relativeSpace X.hom).obj (Y ⨯ Z)))
    (triviality : ∀ D : LineBundle (X ⨯ (Y ⨯ Z)).left,
      Nonempty ((Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj D.obj ≅
        structureSheaf (Y ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj D.obj ≅
        structureSheaf (X ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj D.obj ≅
        structureSheaf (X ⨯ Y).left) →
      Nonempty (D.obj ≅ structureSheaf (X ⨯ (Y ⨯ Z)).left))
    (q r : RigidifiedLineBundle.Classes X.hom x₀.left (overSection_comp X x₀) (Y ⨯ Z))
    (h₂ : RigidifiedLineBundle.classesPullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.secondAxis Y Z y₀) q =
      RigidifiedLineBundle.classesPullback X.hom x₀.left (overSection_comp X x₀)
        (CubeFace.secondAxis Y Z y₀) r)
    (h₃ : RigidifiedLineBundle.classesPullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.thirdAxis Y Z z₀) q =
      RigidifiedLineBundle.classesPullback X.hom x₀.left (overSection_comp X x₀)
        (CubeFace.thirdAxis Y Z z₀) r) : q = r := by
  apply RigidifiedLineBundle.classes_eq_of_threePullbackTriviality preservation
    X.hom x₀.left (overSection_comp X x₀)
    (CubeFace.secondAxis Y Z y₀) (CubeFace.thirdAxis Y Z z₀) comparison
    (fun D ⟨τ₁⟩ ⟨τ₂⟩ ⟨τ₃⟩ ↦
      ⟨CubeRelativeTransport.relativeTrivializationOfCubeTriviality X Y Z x₀ y₀ z₀
        triviality D τ₁ τ₂ τ₃⟩) q r h₂ h₃

end Langlands.AlgebraicGeometry.Picard
