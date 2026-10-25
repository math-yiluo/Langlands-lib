import Langlands.AlgebraicGeometry.Picard.CubeRelativeTransport
import Langlands.AlgebraicGeometry.Picard.RigidificationAdjustment
import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality

/-! # Actual cube trivialization from a universal family and parameter rigidity -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open RigidifiedLineBundle CubeRelativeTransport

variable {S : Scheme.{u}} (X Y Z : Over S)
  (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
  (z₀ : Over.mk (𝟙 S) ⟶ Z)
  {P : Over S}
  (U : relative X.hom x₀.left (overSection_comp X x₀) P)
  (hU : IsUniversal X.hom x₀.left (overSection_comp X x₀) U)

/-- Three ordinary face trivializations give an actual trivialization of the cube
when a universal rigidified family and two-axis rigidity are supplied. -/
def cubeTrivializationOfUniversalFamily
    (rigidity : ∀ g : Y ⨯ Z ⟶ P,
      CubeFace.secondAxis Y Z y₀ ≫ g =
        Over.mkIdTerminal.from Z ≫
          trivialParameter X.hom x₀.left (overSection_comp X x₀) U hU →
      CubeFace.thirdAxis Y Z z₀ ≫ g =
        Over.mkIdTerminal.from Y ≫
          trivialParameter X.hom x₀.left (overSection_comp X x₀) U hU →
      g = Over.mkIdTerminal.from (Y ⨯ Z) ≫
        trivialParameter X.hom x₀.left (overSection_comp X x₀) U hU)
    (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (τ₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left)
    (τ₂ : (Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (X ⨯ Z).left)
    (τ₃ : (Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (X ⨯ Y).left) :
    L.obj ≅ Langlands.Scheme.Modules.structureSheaf (X ⨯ (Y ⨯ Z)).left := by
  let M := cubeRigidified X Y Z x₀ L τ₁
  let e₂ := trivialIsoOfCarrierIso
    ((relativeProjection X.hom).app Z)
    ((relativeSection X.hom x₀.left (overSection_comp X x₀)).app Z)
    (relativeSection_projection X.hom x₀.left (overSection_comp X x₀) Z)
    ((relativePullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.secondAxis Y Z y₀)).obj M)
    (cubeSecondTrivialization X Y Z x₀ y₀ L τ₁ τ₂)
  let e₃ := trivialIsoOfCarrierIso
    ((relativeProjection X.hom).app Y)
    ((relativeSection X.hom x₀.left (overSection_comp X x₀)).app Y)
    (relativeSection_projection X.hom x₀.left (overSection_comp X x₀) Y)
    ((relativePullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.thirdAxis Y Z z₀)).obj M)
    (cubeThirdTrivialization X Y Z x₀ z₀ L τ₁ τ₃)
  let e := trivialIsoOfTwoRestrictions X.hom x₀.left (overSection_comp X x₀)
    U hU (CubeFace.secondAxis Y Z y₀) (CubeFace.thirdAxis Y Z z₀)
    rigidity M e₂ e₃
  exact cubeRecoverTrivialization X Y Z x₀ L τ₁
    (((RigidifiedLineBundle.forget _).mapIso e) |> (LineBundle.forget _).mapIso)

end Langlands.AlgebraicGeometry.Picard
