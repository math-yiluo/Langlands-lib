import Mathlib.Algebra.Homology.Functor

/-! # Homology of a diagram of complexes -/

noncomputable section

universe uJ vJ uC vC uι

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {ι : Type uι} (c : ComplexShape ι) (q : ι)

/-- Computing homology cover by cover agrees with homology in the diagram category,
naturally in complexes and with all index transitions retained. -/
def diagramHomologyIso :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight J (HomologicalComplex C c) C).obj
          (HomologicalComplex.homologyFunctor C c q) ≅
      HomologicalComplex.homologyFunctor (J ⥤ C) c q :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun j => (K.sc q).mapHomologyIso ((evaluation J C).obj j))
      (by
        intro i j a
        change HomologicalComplex.homologyMap (K.asFunctor.map a) q ≫
            ((K.sc q).mapHomologyIso ((evaluation J C).obj j)).hom =
          ((K.sc q).mapHomologyIso ((evaluation J C).obj i)).hom ≫
            ((evaluation J C).map a).app (K.sc q).homology
        rw [NatTrans.app_homology ((evaluation J C).map a) (K.sc q)]
        simp
        rfl))
    (by
      intro K L f
      apply NatTrans.ext
      funext j
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor (J ⥤ C) c q).map f)
        ((evaluation J C).obj j))

/-- Each component is the canonical homology comparison for exact evaluation. -/
@[simp]
theorem diagramHomologyIso_hom_app
    (K : HomologicalComplex (J ⥤ C) c) (j : J) :
    ((diagramHomologyIso (J := J) (C := C) c q).hom.app K).app j =
      ((K.sc q).mapHomologyIso ((evaluation J C).obj j)).hom := rfl

/-- The comparison commutes with homology of every index transition chain map. -/
@[reassoc]
theorem diagramHomologyIso_transition
    (K : HomologicalComplex (J ⥤ C) c) {i j : J} (a : i ⟶ j) :
    HomologicalComplex.homologyMap (K.asFunctor.map a) q ≫
        ((diagramHomologyIso c q).hom.app K).app j =
      ((diagramHomologyIso c q).hom.app K).app i ≫ (K.homology q).map a :=
  ((diagramHomologyIso c q).hom.app K).naturality a

/-- The comparison also commutes with homology of chain maps between diagram complexes. -/
@[reassoc]
theorem diagramHomologyIso_naturality
    {K L : HomologicalComplex (J ⥤ C) c} (f : K ⟶ L) (j : J) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app j) q ≫
        ((diagramHomologyIso c q).hom.app L).app j =
      ((diagramHomologyIso c q).hom.app K).app j ≫
        (HomologicalComplex.homologyMap f q).app j :=
  NatTrans.congr_app ((diagramHomologyIso c q).hom.naturality f) j

end Langlands.Cohomology
