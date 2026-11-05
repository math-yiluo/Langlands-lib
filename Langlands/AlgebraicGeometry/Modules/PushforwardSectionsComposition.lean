import Langlands.AlgebraicGeometry.Modules.BaseChangeResolution
import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeComposition

/-! # Composition of actual relative sections comparisons -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {Y Z T : Scheme.{u}} {R S V : CommRingCat.{u}}
  (φ : R ⟶ S) (ψ : S ⟶ V)
  (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S) (g'' : T ⟶ Spec V)
  (h : Z ⟶ Y) (j : T ⟶ Z)
  (w : h ≫ g = g' ≫ Spec.map φ)
  (w' : j ≫ g' = g'' ≫ Spec.map ψ)

/-- The actual relative sections comparison for a base-ring square. -/
def relativePushforwardBaseRingIso :
    Scheme.Modules.pushforward h ⋙ relativeGlobalSections g ≅
      relativeGlobalSections g' ⋙ ModuleCat.restrictScalars φ.hom :=
  relativeGlobalSectionsCompIso h g ≪≫
    (relativeGlobalSectionsBaseRingIso φ (h ≫ g) g' w).symm

/-- Actual sections comparisons respect pushforward and scalar-restriction composition. -/
@[reassoc]
lemma relativePushforwardBaseRingIso_comp (M : T.Modules) :
    (relativeGlobalSections g).map ((Scheme.Modules.pushforwardComp j h).hom.app M) ≫
        (relativePushforwardBaseRingIso (φ ≫ ψ) g g'' (j ≫ h)
          (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')).hom.app M ≫
        (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
          ((relativeGlobalSections g'').obj M) =
      (relativePushforwardBaseRingIso φ g g' h w).hom.app
          ((Scheme.Modules.pushforward j).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((relativePushforwardBaseRingIso ψ g' g'' j w').hom.app M) := by
  ext x
  rfl

/-- The actual sections cochain map respects composition, including both
the pushforward and scalar-restriction comparison isomorphisms. -/
@[reassoc]
lemma resolutionSectionsBaseChangeMap_comp
    {K : CochainComplex Y.Modules ℕ} {L : CochainComplex Z.Modules ℕ}
    {P : CochainComplex T.Modules ℕ}
    (t : K ⟶ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).obj L)
    (s : L ⟶ ((Scheme.Modules.pushforward j).mapHomologicalComplex _).obj P) :
    resolutionSectionsBaseChangeMap (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')
        (t ≫ ((Scheme.Modules.pushforward h).mapHomologicalComplex _).map s ≫
          (Functor.mapHomologicalComplexCompIso
            (Scheme.Modules.pushforwardComp j h) _).hom.app P) ≫
        (Functor.mapHomologicalComplexCompIso
          (ModuleCat.restrictScalarsComp φ.hom ψ.hom).symm _).inv.app
          (((relativeGlobalSections g'').mapHomologicalComplex _).obj P) =
      resolutionSectionsBaseChangeMap φ g g' h w t ≫
        ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex _).map
          (resolutionSectionsBaseChangeMap ψ g' g'' j w' s) := by
  apply HomologicalComplex.hom_ext
  intro q
  change (relativeGlobalSections g).map
        (t.f q ≫ (Scheme.Modules.pushforward h).map (s.f q) ≫
          (Scheme.Modules.pushforwardComp j h).hom.app (P.X q)) ≫
      (relativePushforwardBaseRingIso (φ ≫ ψ) g g'' (j ≫ h)
        (sectionsBaseChangeSquare_comp φ ψ g g' g'' h j w w')).hom.app (P.X q) ≫
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom.app
        ((relativeGlobalSections g'').obj (P.X q)) =
    ((relativeGlobalSections g).map (t.f q) ≫
      (relativePushforwardBaseRingIso φ g g' h w).hom.app (L.X q)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((relativeGlobalSections g').map (s.f q) ≫
          (relativePushforwardBaseRingIso ψ g' g'' j w').hom.app (P.X q))
  simp only [Functor.map_comp, Category.assoc]
  rw [relativePushforwardBaseRingIso_comp φ ψ g g' g'' h j w w']
  have hn := (relativePushforwardBaseRingIso φ g g' h w).hom.naturality (s.f q)
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
    Category.assoc] using
    congrArg (fun z => (relativeGlobalSections g).map (t.f q) ≫ z ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((relativePushforwardBaseRingIso ψ g' g'' j w').hom.app (P.X q))) hn

end Langlands.AlgebraicGeometry.Modules.DerivedSections
