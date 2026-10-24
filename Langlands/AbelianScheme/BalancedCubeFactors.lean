import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Balanced cube factors and their elementary comparison maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.GroupScheme.BalancedCube

variable {S : Scheme.{u}} (G : Grp (Over S))
variable {T U : Over S}

/-- Pullback of the underlying actual line bundle along a map over the base. -/
abbrev pull (L : LineBundle G.X.left) (a : T ⟶ G.X) : T.left.Modules :=
  (Scheme.Modules.pullback a.left).obj L.obj

/-- The four positive factors, with the exact association of the balanced target. -/
def positive (L : LineBundle G.X.left) (f g h : T ⟶ G.X) : T.left.Modules :=
  tensorObj (pull G L (f * g * h))
    (tensorObj (pull G L f) (tensorObj (pull G L g) (pull G L h)))

/-- The three pair factors, with the exact association of the balanced target. -/
def negative (L : LineBundle G.X.left) (f g h : T ⟶ G.X) : T.left.Modules :=
  tensorObj (pull G L (f * g))
    (tensorObj (pull G L (f * h)) (pull G L (g * h)))

/-- The positive tensor is a line bundle when the canonical tensor comparison is invertible. -/
def positiveLineBundle (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (L : LineBundle G.X.left) (f g h : T ⟶ G.X) : LineBundle T.left :=
  ⟨positive G L f g h, (L.property.pullback _).tensor preservation
    ((L.property.pullback _).tensor preservation
      ((L.property.pullback _).tensor preservation (L.property.pullback _)))⟩

/-- The negative tensor is a line bundle under the same explicit hypothesis. -/
def negativeLineBundle (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (L : LineBundle G.X.left) (f g h : T ⟶ G.X) : LineBundle T.left :=
  ⟨negative G L f g h, (L.property.pullback _).tensor preservation
    ((L.property.pullback _).tensor preservation (L.property.pullback _))⟩

private def pairIso {X : Scheme.{u}} {A B C D : X.Modules}
    (e : A ≅ B) (d : C ≅ D) : tensorObj A C ≅ tensorObj B D :=
  (tensorFunctor X).mapIso (e.prod d)

/-- A trivialization of the constant factor gives the first face comparison. -/
def firstUnitIso (L : LineBundle G.X.left) (g h : T ⟶ G.X)
    (e : pull G L (1 : T ⟶ G.X) ≅ structureSheaf T.left) :
    positive G L 1 g h ≅ negative G L 1 g h := by
  simp only [positive, negative, one_mul]
  exact pairIso (Iso.refl _) (pairIso e (Iso.refl _) ≪≫ tensorLeftUnitor _) ≪≫
    tensorComm _ _ ≪≫ tensorAssociator _ _ _

/-- A trivialization of the constant factor gives the second face comparison. -/
def secondUnitIso (L : LineBundle G.X.left) (f h : T ⟶ G.X)
    (e : pull G L (1 : T ⟶ G.X) ≅ structureSheaf T.left) :
    positive G L f 1 h ≅ negative G L f 1 h := by
  simp only [positive, negative, one_mul, mul_one]
  exact pairIso (Iso.refl _)
      (pairIso (Iso.refl _) (pairIso e (Iso.refl _) ≪≫ tensorLeftUnitor _)) ≪≫
    (tensorAssociator _ _ _).symm ≪≫
      pairIso (tensorComm _ _) (Iso.refl _) ≪≫ tensorAssociator _ _ _

/-- A trivialization of the constant factor gives the third face comparison. -/
def thirdUnitIso (L : LineBundle G.X.left) (f g : T ⟶ G.X)
    (e : pull G L (1 : T ⟶ G.X) ≅ structureSheaf T.left) :
    positive G L f g 1 ≅ negative G L f g 1 := by
  simp only [positive, negative, mul_one]
  exact pairIso (Iso.refl _)
    (pairIso (Iso.refl _) (pairIso (Iso.refl _) e ≪≫ tensorRightUnitor _))

/-- Pullback of a single factor along a map in the slice. -/
def pullPullIso (L : LineBundle G.X.left) (k : U ⟶ T) (a : T ⟶ G.X) :
    (Scheme.Modules.pullback k.left).obj (pull G L a) ≅ pull G L (k ≫ a) :=
  (Scheme.Modules.pullbackComp k.left a.left).app L.obj

private def pullTensorIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (k : U ⟶ T) (M N : T.left.Modules) :
    (Scheme.Modules.pullback k.left).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback k.left).obj M)
        ((Scheme.Modules.pullback k.left).obj N) := by
  letI := preservation k.left
  exact (asIso (pullbackTensorComparison k.left)).app (M, N)

/-- Pullback of the positive tensor, with no geometric condition on the new domain. -/
def pullPositiveIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (L : LineBundle G.X.left) (k : U ⟶ T) (f g h : T ⟶ G.X) :
    (Scheme.Modules.pullback k.left).obj (positive G L f g h) ≅
      positive G L (k ≫ f) (k ≫ g) (k ≫ h) := by
  simpa only [positive, MonObj.comp_mul] using
    (pullTensorIso preservation k (pull G L (f * g * h))
      (tensorObj (pull G L f) (tensorObj (pull G L g) (pull G L h))) ≪≫
      pairIso (pullPullIso G L k (f * g * h))
        (pullTensorIso preservation k (pull G L f)
          (tensorObj (pull G L g) (pull G L h)) ≪≫
          pairIso (pullPullIso G L k f)
            (pullTensorIso preservation k (pull G L g) (pull G L h) ≪≫
              pairIso (pullPullIso G L k g) (pullPullIso G L k h))))

/-- Pullback of the pair tensor, with the target's pair ordering unchanged. -/
def pullNegativeIso (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (L : LineBundle G.X.left) (k : U ⟶ T) (f g h : T ⟶ G.X) :
    (Scheme.Modules.pullback k.left).obj (negative G L f g h) ≅
      negative G L (k ≫ f) (k ≫ g) (k ≫ h) := by
  simpa only [negative, MonObj.comp_mul] using
    (pullTensorIso preservation k (pull G L (f * g))
      (tensorObj (pull G L (f * h)) (pull G L (g * h))) ≪≫
      pairIso (pullPullIso G L k (f * g))
        (pullTensorIso preservation k (pull G L (f * h)) (pull G L (g * h)) ≪≫
          pairIso (pullPullIso G L k (f * h)) (pullPullIso G L k (g * h))))

end Langlands.GroupScheme.BalancedCube
