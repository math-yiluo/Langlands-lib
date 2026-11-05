import Langlands.Geometry.EtaleGeometricCoefficientReindex

/-! # Canonical geometric coefficients from a sheaf on the base -/

noncomputable section

universe u v w v' w'

set_option autoImplicit false

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z W : Scheme.{u}} (R : Type u) [CommRing R]

/-- Equality transports of actual inverse images compose. -/
theorem inverseImageCongr_trans_app {f g k : Z ⟶ X} (e : f = g) (e' : g = k)
    (M : ModuleSheaf X R) :
    (inverseImageCongr R e).hom.app M ≫ (inverseImageCongr R e').hom.app M =
      (inverseImageCongr R (e.trans e')).hom.app M := by
  subst g
  subst k
  simp

/-- The actual composition comparison respects equality in its first map. -/
theorem inverseImageComp_congr_left_app {f f' : Z ⟶ X} (e : f = f') (g : W ⟶ Z)
    (M : ModuleSheaf X R) :
    (inverseImage g R).map ((inverseImageCongr R e).hom.app M) ≫
        (inverseImageComp R f' g).hom.app M =
      (inverseImageComp R f g).hom.app M ≫
        (inverseImageCongr R (congrArg (fun k => g ≫ k) e)).hom.app M := by
  subst f'
  simp

/-- The actual composition comparison respects equality in its second map. -/
theorem inverseImageComp_congr_right_app (f : Z ⟶ X) {g g' : W ⟶ Z} (e : g = g')
    (M : ModuleSheaf X R) :
    (inverseImageCongr R e).hom.app ((inverseImage f R).obj M) ≫
        (inverseImageComp R f g').hom.app M =
      (inverseImageComp R f g).hom.app M ≫
        (inverseImageCongr R (congrArg (fun k => k ≫ f) e)).hom.app M := by
  subst g'
  simp

/-- Pullback of coefficients along a commuting triangle of arbitrary schemes. -/
def projectionInverseImageIso (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y)
    (e : f ≫ p = q) :
    inverseImage p R ⋙ inverseImage f R ≅ inverseImage q R :=
  inverseImageComp R p f ≪≫ inverseImageCongr R e

/-- An identity triangle induces the actual inverse-image identity constraint. -/
theorem projectionInverseImageIso_id (p : Y ⟶ X) (f : Y ⟶ Y)
    (e : f ≫ p = p) (e1 : f = 𝟙 Y) (M : ModuleSheaf X R) :
    (projectionInverseImageIso R p p f e).hom.app M =
      (inverseImageCongr R e1).hom.app ((inverseImage p R).obj M) ≫
        (inverseImageId R Y).hom.app ((inverseImage p R).obj M) := by
  subst f
  have hi := congrArg (fun t => t.app M) (inverseImageComp_id_source R p)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app] at hi
  replace hi := hi.trans (Category.comp_id _)
  simpa only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app,
    inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using hi

/-- Successive commuting triangles give the original inverse-image composition
constraint, with equality transport of the composite arrow retained. -/
theorem projectionInverseImageIso_comp (p : Y ⟶ X) (q : Z ⟶ X) (r : W ⟶ X)
    (f : Z ⟶ Y) (g : W ⟶ Z) (k : W ⟶ Y)
    (ef : f ≫ p = q) (eg : g ≫ q = r) (ek : k ≫ p = r)
    (efg : g ≫ f = k) (M : ModuleSheaf X R) :
    (inverseImage g R).map ((projectionInverseImageIso R p q f ef).hom.app M) ≫
        (projectionInverseImageIso R q r g eg).hom.app M =
      (inverseImageComp R f g).hom.app ((inverseImage p R).obj M) ≫
        (inverseImageCongr R efg).hom.app ((inverseImage p R).obj M) ≫
        (projectionInverseImageIso R p r k ek).hom.app M := by
  have ha := congrArg (fun t => t.app M) (inverseImageComp_assoc R p f g)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  dsimp only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app]
  calc
    _ = (inverseImage g R).map ((inverseImageComp R p f).hom.app M) ≫
        ((inverseImage g R).map ((inverseImageCongr R ef).hom.app M) ≫
          (inverseImageComp R q g).hom.app M) ≫
            (inverseImageCongr R eg).hom.app M := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (inverseImage g R).map ((inverseImageComp R p f).hom.app M) ≫
        ((inverseImageComp R (f ≫ p) g).hom.app M ≫
          (inverseImageCongr R (congrArg (fun t => g ≫ t) ef)).hom.app M) ≫
            (inverseImageCongr R eg).hom.app M := by
      rw [inverseImageComp_congr_left_app R ef g M]
    _ = ((inverseImage g R).map ((inverseImageComp R p f).hom.app M) ≫
          (inverseImageComp R (f ≫ p) g).hom.app M) ≫
        (inverseImageCongr R (congrArg (fun t => g ≫ t) ef)).hom.app M ≫
          (inverseImageCongr R eg).hom.app M := by simp only [Category.assoc]
    _ = _ := by
      rw [ha]
      simp only [Category.assoc]
      rw [← Category.assoc ((inverseImageCongr R efg).hom.app _)
        ((inverseImageComp R p k).hom.app M),
        inverseImageComp_congr_right_app R p efg M]
      simp only [Category.assoc]
      rw [inverseImageCongr_trans_app, inverseImageCongr_trans_app,
        inverseImageCongr_trans_app]

end Langlands.Geometry.EtaleInverseImage

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable {X : Scheme.{u}} (R : Type u) [CommRing R]
variable (π : (Functor.const J).obj (Opposite.op X) ⟶ S)

/-- The original projection at a diagram vertex, as an actual scheme map. -/
abbrev baseProjection (i : J) : (S.obj i).unop ⟶ X := (π.app i).unop

/-- Naturality of the projection is the original commuting scheme triangle. -/
theorem baseProjection_triangle {i j : J} (a : i ⟶ j) :
    (S.map a).unop ≫ baseProjection π i = baseProjection π j := by
  have h := congrArg Quiver.Hom.unop (π.naturality a)
  simpa using h.symm

/-- The canonical coefficient transition before evaluating at a base sheaf. -/
def baseProjectionInverseImageIso {i j : J} (a : i ⟶ j) :
    inverseImage (baseProjection π i) R ⋙ diagramInverseImage R S a ≅
      inverseImage (baseProjection π j) R :=
  projectionInverseImageIso R _ _ _ (baseProjection_triangle π a)

/-- An arbitrary original base sheaf gives compatible actual geometric
coefficients on every vertex, with the cocycle proved from inverse-image
coherence rather than supplied as input. -/
def canonicalCoefficients (M : ModuleSheaf X R) : CoefficientDiagram R S where
  obj i := (inverseImage (baseProjection π i) R).obj M
  map a := (baseProjectionInverseImageIso R π a).hom.app M
  map_id i := projectionInverseImageIso_id R (baseProjection π i) _
    (baseProjection_triangle π (𝟙 i))
    (congrArg Quiver.Hom.unop (S.map_id i)) M
  map_comp a b := by
    simpa only [baseProjectionInverseImageIso, diagramInverseImageComp,
      diagramInverseImage, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
      (projectionInverseImageIso_comp R
        (baseProjection π _) (baseProjection π _) (baseProjection π _)
        (S.map a).unop (S.map b).unop (S.map (a ≫ b)).unop
        (baseProjection_triangle π a) (baseProjection_triangle π b)
        (baseProjection_triangle π (a ≫ b))
        (congrArg Quiver.Hom.unop (S.map_comp a b)).symm M).symm

/-- Every morphism of original base sheaves gives its actual inverse images at
all vertices, commuting with the constructed coefficient transitions. -/
def canonicalCoefficientsMap {M N : ModuleSheaf X R} (α : M ⟶ N) :
    canonicalCoefficients R π M ⟶ canonicalCoefficients R π N where
  app i := (inverseImage (baseProjection π i) R).map α
  comm a := ((baseProjectionInverseImageIso R π a).hom.naturality α).symm

/-- Pullback from the base is a functor into actual geometric coefficient
diagrams, for all base sheaves and every base sheaf morphism. -/
def canonicalCoefficientsFunctor : ModuleSheaf X R ⥤ CoefficientDiagram R S where
  obj := canonicalCoefficients R π
  map := canonicalCoefficientsMap R π
  map_id M := by
    apply CoefficientDiagram.Hom.ext
    funext i
    exact (inverseImage (baseProjection π i) R).map_id M
  map_comp α β := by
    apply CoefficientDiagram.Hom.ext
    funext i
    exact (inverseImage (baseProjection π i) R).map_comp α β

/-- The vertex coefficient is the inverse image of the original base sheaf. -/
@[simp] theorem canonicalCoefficients_obj (M : ModuleSheaf X R) (i : J) :
    (canonicalCoefficients R π M).obj i =
      (inverseImage (baseProjection π i) R).obj M := rfl

/-- The transition uses the original composition and triangle comparisons. -/
theorem canonicalCoefficients_map (M : ModuleSheaf X R) {i j : J} (a : i ⟶ j) :
    (canonicalCoefficients R π M).map a =
      (inverseImageComp R (baseProjection π i) (S.map a).unop).hom.app M ≫
        (inverseImageCongr R (baseProjection_triangle π a)).hom.app M := rfl

/-- Each canonical coefficient transition is an isomorphism even when the
original scheme map is not étale or invertible. -/
instance canonicalCoefficients_map_isIso (M : ModuleSheaf X R)
    {i j : J} (a : i ⟶ j) : IsIso ((canonicalCoefficients R π M).map a) :=
  inferInstanceAs (IsIso ((baseProjectionInverseImageIso R π a).hom.app M))

/-- The canonical map at a vertex is the actual inverse image of the original
base sheaf morphism. -/
@[simp] theorem canonicalCoefficientsMap_app {M N : ModuleSheaf X R}
    (α : M ⟶ N) (i : J) :
    (canonicalCoefficientsMap R π α).app i =
      (inverseImage (baseProjection π i) R).map α := rfl

/-- Evaluation of the canonical coefficient functor recovers the original
inverse-image functor on every object and morphism. -/
def canonicalCoefficientsEvaluationIso (i : J) :
    canonicalCoefficientsFunctor R π ⋙ CoefficientDiagram.evaluation i ≅
      inverseImage (baseProjection π i) R :=
  Iso.refl _

/-- Both directions of the evaluation comparison are actual identity maps. -/
@[simp] theorem canonicalCoefficientsEvaluationIso_hom_app
    (i : J) (M : ModuleSheaf X R) :
    (canonicalCoefficientsEvaluationIso R π i).hom.app M = 𝟙 _ := rfl

@[simp] theorem canonicalCoefficientsEvaluationIso_inv_app
    (i : J) (M : ModuleSheaf X R) :
    (canonicalCoefficientsEvaluationIso R π i).inv.app M = 𝟙 _ := rfl

variable {K : Type v'} [Category.{w'} K] (F : K ⥤ J)

/-- The base projection itself reindexes by its original components. -/
def reindexBaseProjection :
    (Functor.const K).obj (Opposite.op X) ⟶ F ⋙ S :=
  Functor.whiskerLeft F π

/-- Reindexing canonical coefficients retains the original sheaves and maps
definitionally, including the triangle equality comparisons. -/
theorem canonicalCoefficients_reindex (M : ModuleSheaf X R) :
    CoefficientDiagram.reindex F (canonicalCoefficients R π M) =
      canonicalCoefficients R (reindexBaseProjection π F) M := rfl

/-- Canonical pullback coefficients commute with every index functor,
naturally in all original base coefficients. -/
def canonicalCoefficientsReindexIso :
    canonicalCoefficientsFunctor R π ⋙ CoefficientDiagram.reindexFunctor F ≅
      canonicalCoefficientsFunctor R (reindexBaseProjection π F) :=
  Iso.refl _

/-- The reindexing comparison has the original identity coefficient maps. -/
@[simp] theorem canonicalCoefficientsReindexIso_hom_app_app
    (M : ModuleSheaf X R) (i : K) :
    ((canonicalCoefficientsReindexIso R π F).hom.app M).app i = 𝟙 _ := rfl

@[simp] theorem canonicalCoefficientsReindexIso_inv_app_app
    (M : ModuleSheaf X R) (i : K) :
    ((canonicalCoefficientsReindexIso R π F).inv.app M).app i = 𝟙 _ := rfl

end Langlands.Geometry.EtaleGeometricDiagram
