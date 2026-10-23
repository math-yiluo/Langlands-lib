import Langlands.Geometry.EtaleDerivedPullbackFunctoriality

/-!
# Cohomology diagrams over varying schemes

Compatible module sheaves on a contravariant diagram of schemes induce a
diagram of ordinary étale cohomology modules.
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} (R : Type u) [CommRing R]

/-- Equal scheme morphisms give canonically identified restriction functors. -/
def restrictionCongr {f g : Y ⟶ X} [Etale f] [Etale g] (h : f = g) :
    restriction f (ModuleCat.{u} R) ≅ restriction g (ModuleCat.{u} R) := by
  subst g
  exact Iso.refl _

/-- Cohomology pullback respects equality of its underlying scheme morphism. -/
theorem cohomologyMap_congr {f g : Y ⟶ X} [Etale f] [Etale g] (h : f = g)
    (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (cohomologyMap f R q).app F ≫
        (EtaleDerivedSections.cohomology Y R q).map
          ((restrictionCongr R h).hom.app F) =
      (cohomologyMap g R q).app F := by
  subst g
  simp [restrictionCongr]

/-- Composition of pullbacks with arbitrary coefficient-sheaf maps. -/
theorem cohomologyMapWithCoefficients_comp
    (f : Y ⟶ X) [Etale f] (g : Z ⟶ Y) [Etale g] (q : ℕ)
    {F : EtaleDerivedSections.ModuleSheaf X R}
    {G : EtaleDerivedSections.ModuleSheaf Y R}
    {H : EtaleDerivedSections.ModuleSheaf Z R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G)
    (β : (restriction g (ModuleCat.{u} R)).obj G ⟶ H) :
    cohomologyMapWithCoefficients f R q α ≫
        cohomologyMapWithCoefficients g R q β =
      cohomologyMapWithCoefficients (g ≫ f) R q
        ((restrictionComp f (ModuleCat.{u} R) g).inv.app F ≫
          (restriction g (ModuleCat.{u} R)).map α ≫ β) := by
  dsimp only [cohomologyMapWithCoefficients]
  rw [← cohomologyMap_comp f R g q F]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(EtaleDerivedSections.cohomology Z R q).map_id]
  rw [Category.id_comp]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun k => (cohomologyMap f R q).app F ≫ k ≫
      (EtaleDerivedSections.cohomology Z R q).map β)
    ((cohomologyMap g R q).naturality α)

variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]

/-- Restriction in the direction of an arrow of the opposite scheme diagram. -/
abbrev diagramRestriction {i j : J} (a : i ⟶ j) :=
  restriction (S.map a).unop (ModuleCat.{u} R)

/-- The diagram's identity law identifies restriction with the identity functor. -/
def diagramRestrictionId (i : J) :
    diagramRestriction R S (𝟙 i) ≅
      𝟭 (EtaleDerivedSections.ModuleSheaf (S.obj i).unop R) :=
  restrictionCongr R (congrArg Quiver.Hom.unop (S.map_id i)) ≪≫
    restrictionId (ModuleCat.{u} R)

/-- The diagram's composition law identifies successive restrictions. -/
def diagramRestrictionComp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    diagramRestriction R S a ⋙ diagramRestriction R S b ≅
      diagramRestriction R S (a ≫ b) :=
  restrictionComp (S.map a).unop (ModuleCat.{u} R) (S.map b).unop ≪≫
    restrictionCongr R (congrArg Quiver.Hom.unop (S.map_comp a b)).symm

/-- Pullback along a diagram identity acts identically after identification. -/
theorem diagramCohomologyMap_id (i : J) (q : ℕ)
    (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop R) :
    (cohomologyMap (S.map (𝟙 i)).unop R q).app F ≫
        (EtaleDerivedSections.cohomology (S.obj i).unop R q).map
          ((diagramRestrictionId R S i).hom.app F) = 𝟙 _ := by
  dsimp only [diagramRestrictionId, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, cohomologyMap_congr]
  exact cohomologyMap_id R q F

/-- Pullback along a diagram composite agrees with the successive pullbacks. -/
theorem diagramCohomologyMap_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop R) :
    (cohomologyMap (S.map a).unop R q).app F ≫
        (cohomologyMap (S.map b).unop R q).app ((diagramRestriction R S a).obj F) ≫
        (EtaleDerivedSections.cohomology (S.obj k).unop R q).map
          ((diagramRestrictionComp R S a b).hom.app F) =
      (cohomologyMap (S.map (a ≫ b)).unop R q).app F := by
  dsimp only [diagramRestrictionComp, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp]
  have e : (S.map b).unop ≫ (S.map a).unop = (S.map (a ≫ b)).unop :=
    (congrArg Quiver.Hom.unop (S.map_comp a b)).symm
  calc
    _ = (cohomologyMap ((S.map b).unop ≫ (S.map a).unop) R q).app F ≫
        (EtaleDerivedSections.cohomology (S.obj k).unop R q).map
          ((restrictionCongr R e).hom.app F) := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (EtaleDerivedSections.cohomology (S.obj k).unop R q).map
          ((restrictionCongr R e).hom.app F))
        (cohomologyMap_comp (S.map a).unop R (S.map b).unop q F)
    _ = _ := cohomologyMap_congr R e q F

/-- Actual coefficient sheaves with restriction-compatible transition morphisms.
The laws concern sheaves; no cohomology maps or laws are assumed. -/
structure CoefficientDiagram where
  obj (i : J) : EtaleDerivedSections.ModuleSheaf (S.obj i).unop R
  map {i j : J} (a : i ⟶ j) : (diagramRestriction R S a).obj (obj i) ⟶ obj j
  map_id (i : J) : map (𝟙 i) = (diagramRestrictionId R S i).hom.app (obj i)
  map_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    (diagramRestrictionComp R S a b).hom.app (obj i) ≫ map (a ≫ b) =
      (diagramRestriction R S b).map (map a) ≫ map b

namespace CoefficientDiagram

variable {R S}

/-- The cohomology modules and transition maps of compatible coefficient sheaves. -/
def cohomology (D : CoefficientDiagram R S) (q : ℕ) : J ⥤ ModuleCat.{u} R where
  obj i := (EtaleDerivedSections.cohomology (S.obj i).unop R q).obj (D.obj i)
  map a := cohomologyMapWithCoefficients (S.map a).unop R q (D.map a)
  map_id i := by
    dsimp only [cohomologyMapWithCoefficients]
    rw [D.map_id]
    exact diagramCohomologyMap_id R S i q (D.obj i)
  map_comp {i j k} a b := by
    dsimp only [cohomologyMapWithCoefficients]
    rw [← diagramCohomologyMap_comp R S a b q (D.obj i)]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, D.map_comp]
    simp only [CategoryTheory.Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => (cohomologyMap (S.map a).unop R q).app (D.obj i) ≫ t ≫
        (EtaleDerivedSections.cohomology (S.obj k).unop R q).map (D.map b))
      ((cohomologyMap (S.map b).unop R q).naturality (D.map a)).symm

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
