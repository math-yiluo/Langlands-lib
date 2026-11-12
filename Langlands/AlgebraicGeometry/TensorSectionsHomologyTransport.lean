import Langlands.AlgebraicGeometry.TensorSectionsHomology
import Mathlib.Algebra.Homology.Homotopy

/-! # Transport of tensor homology presheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

namespace Langlands.AlgebraicGeometry.TensorSections

variable {R : CommRingCat.{u}}

/-- A map of coefficient complexes induces a map of tensor complexes,
naturally in the coefficient module. -/
def tensorComplexMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    tensorComplex K ⟶ tensorComplex L where
  app A := ((tensorLeft A).mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  naturality A B f := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (whisker_exchange f (φ.f i)).symm

/-- A map of coefficient complexes induces a map of tensor homology presheaves. -/
def homologyPresheafMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (n : ℤ) :
    homologyPresheaf K n ⟶ homologyPresheaf L n :=
  Functor.whiskerRight (Functor.whiskerLeft sectionModules (tensorComplexMap φ))
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
      forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1})

/-- A homotopy equivalence of coefficient complexes induces an isomorphism of
tensor homology presheaves on the entire scheme slice. -/
def homologyPresheafIsoOfHomotopyEquiv {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : HomotopyEquiv K L) (n : ℤ) :
    homologyPresheaf K n ≅ homologyPresheaf L n :=
  NatIso.ofComponents
    (fun T ↦ (uliftFunctor.{u + 1}.mapIso ((forget (ModuleCat.{u} R)).mapIso
      (((tensorLeft (sectionModules.obj T)).mapHomotopyEquiv h).toHomologyIso n))))
    (fun q ↦ (homologyPresheafMap h.hom n).naturality q)

end Langlands.AlgebraicGeometry.TensorSections
