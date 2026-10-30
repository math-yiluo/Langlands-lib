import Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement
import Langlands.Algebra.LocalFiberwiseFlatness
import Langlands.AlgebraicGeometry.StalkEssFinitePresentation
import Langlands.AlgebraicGeometry.FiberStalkFlatness

/-! # The finite-presentation fibrewise flatness criterion -/

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of schemes over a base is flat under the finite-presentation
fibrewise flatness hypotheses of Stacks Project tag 039E. -/
theorem fiberwiseFlatness : FiberwiseFlatnessStatement.{u} := by
  intro S X Y f hXflat hXfinite hYfinite hFibers
  let := hXflat
  let := hXfinite
  let := hYfinite
  apply Flat.of_stalkMap
  intro x
  let R : Type u := S.presheaf.stalk (Y.hom (f.left x))
  let A : Type u := Y.left.presheaf.stalk (f.left x)
  let B : Type u := X.left.presheaf.stalk x
  let g : R →+* A := (Y.hom.stalkMap (f.left x)).hom
  let h : A →+* B := (f.left.stalkMap x).hom
  let : Algebra R A := g.toAlgebra
  let : Algebra A B := h.toAlgebra
  let : Algebra R B := (h.comp g).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Flat (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have hcomp : ((f.left ≫ Y.hom).stalkMap x).hom = h.comp g := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hEB : Langlands.Algebra.EssFinitePresentation R B := by
    have hp := stalkEssFinitePresentation X.left S (f.left ≫ Y.hom) x inferInstance
    change @Langlands.Algebra.EssFinitePresentation R B _ _
      ((f.left ≫ Y.hom).stalkMap x).hom.toAlgebra at hp
    rw [hcomp] at hp
    exact hp
  have hRA : _root_.Algebra.EssFiniteType R A :=
    LocallyOfFiniteType.stalkMap Y.hom (f.left x)
  have hRB : Module.Flat R B := by
    have hp := Flat.stalkMap (f.left ≫ Y.hom) x
    rw [hcomp] at hp
    exact hp
  have hF := fiberStalkFlatness S X Y f x (hFibers (Y.hom (f.left x)))
  have : IsLocalHom (algebraMap R A) :=
    inferInstanceAs <| IsLocalHom (Y.hom.stalkMap (f.left x)).hom
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs <| IsLocalHom (f.left.stalkMap x).hom
  have hAB : Module.Flat A B :=
    (Langlands.Algebra.localFiberwiseFlatness.{u, u, u, u}
      R A B B hEB hRA inferInstance inferInstance hF hRB).2.2
  exact hAB

end Langlands.AlgebraicGeometry
