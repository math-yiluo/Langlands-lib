import Langlands.Geometry.EtaleDerivedPlusPullbackFunctoriality
import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-! # Derived sections of compatible coefficients over varying schemes -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u v w wX wY wZ wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]

/-- Equal geometric morphisms give the same derived pullback after the
canonical identification of their restrictions. -/
theorem derivedSectionsMap_congr {f g : Y ⟶ X} [Etale f] [Etale g] (h : f = g)
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (derivedSectionsMap f R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((restrictionCongr R h).hom.app F) =
      (derivedSectionsMap g R).app F := by
  subst g
  simp [restrictionCongr]

/-- Successive pullbacks with target coefficient morphisms compose in D⁺. -/
theorem derivedSectionsMapWithCoefficients_comp
    (f : Y ⟶ X) [Etale f] (g : Z ⟶ Y) [Etale g]
    {F : EtaleDerivedSections.ModuleSheaf X R}
    {G : EtaleDerivedSections.ModuleSheaf Y R}
    {H : EtaleDerivedSections.ModuleSheaf Z R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G)
    (β : (restriction g (ModuleCat.{u} R)).obj G ⟶ H) :
    derivedSectionsMapWithCoefficients f R α ≫
        derivedSectionsMapWithCoefficients g R β =
      derivedSectionsMapWithCoefficients (g ≫ f) R
        ((restrictionComp f (ModuleCat.{u} R) g).inv.app F ≫
          (restriction g (ModuleCat.{u} R)).map α ≫ β) := by
  dsimp only [derivedSectionsMapWithCoefficients]
  rw [← derivedSectionsMap_comp f R g F]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(EtaleDerivedSectionsPlus.derivedSections Z R).map_id]
  rw [Category.id_comp]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun k => (derivedSectionsMap f R).app F ≫ k ≫
      (EtaleDerivedSectionsPlus.derivedSections Z R).map β)
    ((derivedSectionsMap g R).naturality α)

variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable [∀ i : J, HasDerivedCategory.{wS}
  (EtaleDerivedSections.ModuleSheaf (S.obj i).unop R)]

/-- Derived pullback along a diagram identity is the identity after the
coefficient identity identification. -/
theorem diagramDerivedSectionsMap_id (i : J)
    (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop R) :
    (derivedSectionsMap (S.map (𝟙 i)).unop R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map
          ((diagramRestrictionId R S i).hom.app F) = 𝟙 _ := by
  dsimp only [diagramRestrictionId, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, derivedSectionsMap_congr]
  exact derivedSectionsMap_id R F

/-- Derived pullback respects the composition constraint of a scheme diagram. -/
theorem diagramDerivedSectionsMap_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop R) :
    (derivedSectionsMap (S.map a).unop R).app F ≫
        (derivedSectionsMap (S.map b).unop R).app ((diagramRestriction R S a).obj F) ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
          ((diagramRestrictionComp R S a b).hom.app F) =
      (derivedSectionsMap (S.map (a ≫ b)).unop R).app F := by
  dsimp only [diagramRestrictionComp, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp]
  have e : (S.map b).unop ≫ (S.map a).unop = (S.map (a ≫ b)).unop :=
    (congrArg Quiver.Hom.unop (S.map_comp a b)).symm
  calc
    _ = (derivedSectionsMap ((S.map b).unop ≫ (S.map a).unop) R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
          ((restrictionCongr R e).hom.app F) := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
          ((restrictionCongr R e).hom.app F))
        (derivedSectionsMap_comp (S.map a).unop R (S.map b).unop F)
    _ = _ := derivedSectionsMap_congr R e F

namespace CoefficientDiagram

variable {R S}

/-- Actual bounded-below derived sections of compatible coefficients, with
geometric transition maps followed by the given coefficient maps. -/
def derivedSections (D : CoefficientDiagram R S) :
    J ⥤ DerivedCategory.Plus (ModuleCat.{u} R) where
  obj i := (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).obj (D.obj i)
  map a := derivedSectionsMapWithCoefficients (S.map a).unop R (D.map a)
  map_id i := by
    dsimp only [derivedSectionsMapWithCoefficients]
    rw [D.map_id]
    exact diagramDerivedSectionsMap_id R S i (D.obj i)
  map_comp {i j k} a b := by
    dsimp only [derivedSectionsMapWithCoefficients]
    rw [← diagramDerivedSectionsMap_comp R S a b (D.obj i)]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, D.map_comp]
    simp only [CategoryTheory.Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => (EtalePullback.derivedSectionsMap (S.map a).unop R).app (D.obj i) ≫ t ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map (D.map b))
      ((EtalePullback.derivedSectionsMap (S.map b).unop R).naturality (D.map a)).symm

/-- Compatible coefficient morphisms induce natural morphisms of actual
derived-section diagrams. -/
def derivedSectionsMap {D E : CoefficientDiagram R S} (α : D ⟶ E) :
    D.derivedSections ⟶ E.derivedSections where
  app i := (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i)
  naturality {i j} a := by
    dsimp only [derivedSections, derivedSectionsMapWithCoefficients]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, α.comm, CategoryTheory.Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => t ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj j).unop R).map (E.map a))
      ((EtalePullback.derivedSectionsMap (S.map a).unop R).naturality (α.app i)).symm

/-- Derived sections form a functor on the actual category of compatible
coefficient diagrams. -/
def derivedSectionsFunctor :
    CoefficientDiagram R S ⥤ (J ⥤ DerivedCategory.Plus (ModuleCat.{u} R)) where
  obj D := D.derivedSections
  map α := derivedSectionsMap α
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map_comp
      (α.app i) (β.app i)

/-- The cohomology of a derived-section diagram is its previously constructed
ordinary cohomology diagram, naturally along every geometric arrow. -/
def derivedSectionsHomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    D.derivedSections ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      D.cohomology q :=
  NatIso.ofComponents
    (fun i => (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).app (D.obj i))
    (fun a => derivedSectionsMapWithCoefficients_homology (S.map a).unop R (D.map a) q)

/-- The recovery of ordinary cohomology is natural also in compatible
coefficient morphisms. -/
def derivedSectionsHomologyFunctorIso (q : ℕ) :
    derivedSectionsFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≅
      cohomologyFunctor q :=
  NatIso.ofComponents (fun D => derivedSectionsHomologyIso D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).hom.naturality
        (α.app i))

/-- Degree-zero derived cohomology recovers ordinary sections as a diagram. -/
def derivedSectionsZeroIso (D : CoefficientDiagram R S) :
    D.derivedSections ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      D.sections :=
  derivedSectionsHomologyIso D 0 ≪≫ cohomologyZeroIso D

/-- Degree-zero recovery is natural in compatible coefficient diagrams. -/
def derivedSectionsZeroFunctorIso :
    derivedSectionsFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≅
      sectionsFunctor :=
  derivedSectionsHomologyFunctorIso 0 ≪≫ cohomologyZeroFunctorIso

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
