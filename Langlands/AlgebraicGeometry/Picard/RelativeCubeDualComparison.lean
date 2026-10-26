import Langlands.AlgebraicGeometry.Picard.RelativeCubeClassComparison
import Langlands.AlgebraicGeometry.Picard.CubeLineBundleComparison
import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Actual dual inverses and the monoidal relative cube comparison -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory CategoryTheory.MonObj

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Ordinary cube triviality detects equality of actual rigidified classes,
using actual line-bundle dual inverses. -/
lemma rigidifiedClasses_eq_of_cubeTrivialityWithDual
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (X Y Z : Over S)
    (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
    (z₀ : Over.mk (𝟙 S) ⟶ Z)
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
  apply RigidifiedLineBundle.classes_eq_of_threePullbackTrivialityWithDual preservation
    X.hom x₀.left (overSection_comp X x₀)
    (CubeFace.secondAxis Y Z y₀) (CubeFace.thirdAxis Y Z z₀)
    (fun D ⟨τ₁⟩ ⟨τ₂⟩ ⟨τ₃⟩ ↦
      ⟨CubeRelativeTransport.relativeTrivializationOfCubeTriviality X Y Z x₀ y₀ z₀
        triviality D τ₁ τ₂ τ₃⟩) q r h₂ h₃

namespace CubeRelativeTransport

variable {S : Scheme.{u}} (Y Z : Over S)

/-- Compare the chosen monoidal parameter product with the categorical product. -/
def parameterProductIso : Y ⊗ Z ≅ Y ⨯ Z where
  hom := prod.lift (CartesianMonoidalCategory.fst Y Z) (CartesianMonoidalCategory.snd Y Z)
  inv := CartesianMonoidalCategory.lift prod.fst prod.snd
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by
    apply prod.hom_ext <;> simp

/-- The second categorical axis transports to the corresponding monoidal pairing. -/
lemma secondAxis_parameterProductIso_inv (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    CubeFace.secondAxis Y Z y₀ ≫ (parameterProductIso Y Z).inv =
      CartesianMonoidalCategory.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [parameterProductIso, CubeFace.secondAxis]

/-- The third categorical axis transports to the corresponding monoidal pairing. -/
lemma thirdAxis_parameterProductIso_inv (z₀ : Over.mk (𝟙 S) ⟶ Z) :
    CubeFace.thirdAxis Y Z z₀ ≫ (parameterProductIso Y Z).inv =
      CartesianMonoidalCategory.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [parameterProductIso, CubeFace.thirdAxis]

end CubeRelativeTransport

namespace RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

private lemma pullback_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V)
    (q : Classes f ε section_eq V) :
    classesPullback f ε section_eq h (classesPullback f ε section_eq k q) =
      classesPullback f ε section_eq (h ≫ k) q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(relativePullbackComp
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq h k).app L⟩

private lemma pullback_id {T : Over S} (q : Classes f ε section_eq T) :
    classesPullback f ε section_eq (𝟙 T) q = q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(relativePullbackId
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε section_eq T).app L⟩

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- An ordinary geometric cube criterion gives two-axis detection on the actual
monoidal parameter product of abelian schemes. -/
lemma rigidifiedClasses_eq_of_ordinaryCubeTriviality
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (A B C : AbelianScheme S)
    (triviality : ∀ D : LineBundle (A.X ⨯ (B.X ⨯ C.X)).left,
      Nonempty ((Scheme.Modules.pullback
        (CubeFace.first A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
          structureSheaf (B.X ⨯ C.X).left) →
      Nonempty ((Scheme.Modules.pullback
        (CubeFace.second A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)).left).obj D.obj ≅
          structureSheaf (A.X ⨯ C.X).left) →
      Nonempty ((Scheme.Modules.pullback
        (CubeFace.third A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)).left).obj D.obj ≅
          structureSheaf (A.X ⨯ B.X).left) →
      Nonempty (D.obj ≅ structureSheaf (A.X ⨯ (B.X ⨯ C.X)).left))
    (q r : RigidifiedClasses A (B.X ⊗ C.X))
    (hB : RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (CartesianMonoidalCategory.lift (𝟙 B.X) (1 : B.X ⟶ C.X)) q =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (𝟙 B.X) (1 : B.X ⟶ C.X)) r)
    (hC : RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
      (CartesianMonoidalCategory.lift (1 : C.X ⟶ B.X) (𝟙 C.X)) q =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (1 : C.X ⟶ B.X) (𝟙 C.X)) r) : q = r := by
  let e := CubeRelativeTransport.parameterProductIso B.X C.X
  let P : {T U : Over S} → (T ⟶ U) → RigidifiedClasses A U → RigidifiedClasses A T :=
    fun h ↦ RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
      (unitSection_comp A) h
  have h : P e.inv q = P e.inv r := by
    apply rigidifiedClasses_eq_of_cubeTrivialityWithDual preservation A.X B.X C.X
      (1 : Over.mk (𝟙 S) ⟶ A.X) (1 : Over.mk (𝟙 S) ⟶ B.X)
      (1 : Over.mk (𝟙 S) ⟶ C.X) triviality
    · change P (CubeFace.secondAxis B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)) (P e.inv q) =
        P (CubeFace.secondAxis B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)) (P e.inv r)
      dsimp only [P]
      rw [RigidifiedLineBundle.pullback_comp, RigidifiedLineBundle.pullback_comp]
      simpa only [e, CubeRelativeTransport.secondAxis_parameterProductIso_inv,
        MonObj.comp_one] using hC
    · change P (CubeFace.thirdAxis B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)) (P e.inv q) =
        P (CubeFace.thirdAxis B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)) (P e.inv r)
      dsimp only [P]
      rw [RigidifiedLineBundle.pullback_comp, RigidifiedLineBundle.pullback_comp]
      simpa only [e, CubeRelativeTransport.thirdAxis_parameterProductIso_inv,
        MonObj.comp_one] using hB
  have h' := congrArg (P e.hom) h
  simpa only [P, RigidifiedLineBundle.pullback_comp, e.hom_inv_id,
    RigidifiedLineBundle.pullback_id] using h'

end Langlands.AbelianScheme
