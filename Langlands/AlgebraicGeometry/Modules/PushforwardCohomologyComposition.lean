import Langlands.AlgebraicGeometry.Modules.PushforwardSectionsComposition
import Langlands.Cohomology.DerivedExactComposition

/-! # Cohomology composition for actual sections cochain maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {Y Z T : Scheme.{u}} {R S V : CommRingCat.{u}}
  (φ : R ⟶ S) (ψ : S ⟶ V)
  (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S) (g'' : T ⟶ Spec V)
  (h : Z ⟶ Y) (j : T ⟶ Z)
  (w : h ≫ g = g' ≫ Spec.map φ)
  (w' : j ≫ g' = g'' ≫ Spec.map ψ)

/-- Homology of the actual sections cochain map, with the exact
restriction-of-scalars homology comparison. -/
def resolutionCohomologyBaseChangeMap
    {K : CochainComplex Y.Modules ℕ} {L : CochainComplex Z.Modules ℕ}
    (t : K ⟶ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).obj L)
    (n : ℕ) :
    (homologyFunctor (ModuleCat R) _ n).obj
        (((relativeGlobalSections g).mapHomologicalComplex _).obj K) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((homologyFunctor (ModuleCat S) _ n).obj
          (((relativeGlobalSections g').mapHomologicalComplex _).obj L)) :=
  (homologyFunctor (ModuleCat R) _ n).map
      (resolutionSectionsBaseChangeMap φ g g' h w t) ≫
    (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
      (((relativeGlobalSections g').mapHomologicalComplex _).obj L) n).hom

/-- The exact homology comparisons retain the canonical scalar-composition
isomorphism. -/
@[reassoc]
lemma restrictScalars_mapHomologyIso_comp (P : CochainComplex (ModuleCat V) ℕ) (n : ℕ) :
    (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars (φ ≫ ψ).hom) P n).hom ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((homologyFunctor (ModuleCat V) _ n).obj P) =
      (homologyFunctor (ModuleCat R) _ n).map
          ((Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp φ.hom ψ.hom).symm _).inv.app P) ≫
        (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
          (((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex _).obj P) n).hom ≫
        (ModuleCat.restrictScalars φ.hom).map
          (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars ψ.hom) P n).hom := by
  have hc := NatTrans.app_homology
    (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom (P.sc n)
  have hi := DerivedPlus.mapHomologyIso_comp_hom
    (ModuleCat.restrictScalars ψ.hom) (ModuleCat.restrictScalars φ.hom) (P.sc n)
  change (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
    ((homologyFunctor (ModuleCat V) _ n).obj P) = _ at hc
  change ((P.sc n).mapHomologyIso
    (ModuleCat.restrictScalars (ψ.hom.comp φ.hom))).hom ≫ _ = _
  rw [hc, Iso.hom_inv_id_assoc, hi]
  rfl

/-- The semilinear cohomology maps respect composition with its canonical
pushforward and scalar-restriction comparisons. -/
@[reassoc]
lemma resolutionCohomologyBaseChangeMap_comp
    {K : CochainComplex Y.Modules ℕ} {L : CochainComplex Z.Modules ℕ}
    {P : CochainComplex T.Modules ℕ}
    (t : K ⟶ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).obj L)
    (s : L ⟶ ((Scheme.Modules.pushforward j).mapHomologicalComplex _).obj P)
    (n : ℕ) :
    resolutionCohomologyBaseChangeMap (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
        (t ≫ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).map s ≫
          (Functor.mapHomologicalComplexCompIso
            (Scheme.Modules.pushforwardComp j h) _).hom.app P) n ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((homologyFunctor (ModuleCat V) _ n).obj
            (((relativeGlobalSections g'').mapHomologicalComplex _).obj P)) =
      resolutionCohomologyBaseChangeMap φ g g' h w t n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (resolutionCohomologyBaseChangeMap ψ g' g'' j w' s n) := by
  have hc := resolutionSectionsBaseChangeMap_comp φ ψ g g' g'' h j w w' t s
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat S) (ComplexShape.up ℕ) n).map
      (resolutionSectionsBaseChangeMap ψ g' g'' j w' s))
    (ModuleCat.restrictScalars φ.hom)
  change (homologyFunctor (ModuleCat R) _ n).map
      (((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
        (resolutionSectionsBaseChangeMap ψ g' g'' j w' s)) ≫
      (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
        (((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex _).obj
          (((relativeGlobalSections g'').mapHomologicalComplex _).obj P)) n).hom =
    (DerivedComparison.mapHomologyIso (ModuleCat.restrictScalars φ.hom)
      (((relativeGlobalSections g').mapHomologicalComplex _).obj L) n).hom ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((homologyFunctor (ModuleCat S) _ n).map
          (resolutionSectionsBaseChangeMap ψ g' g'' j w' s)) at hn
  simp only [resolutionCohomologyBaseChangeMap, Category.assoc]
  rw [restrictScalars_mapHomologyIso_comp φ ψ]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp_assoc]
  rw [reassoc_of% hn]
  rw [Functor.map_comp]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
