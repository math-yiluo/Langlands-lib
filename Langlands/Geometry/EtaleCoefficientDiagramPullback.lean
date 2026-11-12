import Langlands.Geometry.EtaleCanonicalCoefficientDiagram

/-! # Pulling geometric coefficient diagrams back along morphisms of scheme diagrams -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z W : Scheme.{u}} (R : Type u) [CommRing R]

/-- The inverse of an equality transport is the transport along the reversed equality. -/
theorem inverseImageCongr_inv_app {f k : Z ⟶ X} (e : f = k) (M : ModuleSheaf X R) :
    (inverseImageCongr R e).inv.app M = (inverseImageCongr R e.symm).hom.app M := by
  subst e
  simp

/-- The triangle comparison along a top map equal to another one. -/
theorem projectionInverseImageIso_congr_top (p : Y ⟶ X) {q : Z ⟶ X} {f f' : Z ⟶ Y}
    (h : f = f') (e : f ≫ p = q) (e' : f' ≫ p = q) (M : ModuleSheaf X R) :
    (inverseImageCongr R h).hom.app ((inverseImage p R).obj M) ≫
        (projectionInverseImageIso R p q f' e').hom.app M =
      (projectionInverseImageIso R p q f e).hom.app M := by
  subst h
  simp

/-- The triangle comparison followed by transport along an equality of composites. -/
theorem projectionInverseImageIso_congr_comp (p : Y ⟶ X) {q q' : Z ⟶ X} (f : Z ⟶ Y)
    (e : f ≫ p = q) (e' : q = q') (M : ModuleSheaf X R) :
    (projectionInverseImageIso R p q f e).hom.app M ≫ (inverseImageCongr R e').hom.app M =
      (projectionInverseImageIso R p q' f (e.trans e')).hom.app M := by
  subst e'
  simp

/-- Two pasted commuting triangles, in the symmetric form in which both sides are triangle
comparisons. -/
theorem projectionInverseImageIso_paste (p : Y ⟶ X) (q : Z ⟶ X) (r : W ⟶ X)
    (f : Z ⟶ Y) (g : W ⟶ Z) (k : W ⟶ Y)
    (ef : f ≫ p = q) (eg : g ≫ q = r) (ek : k ≫ p = r)
    (efg : g ≫ f = k) (M : ModuleSheaf X R) :
    (inverseImage g R).map ((projectionInverseImageIso R p q f ef).hom.app M) ≫
        (projectionInverseImageIso R q r g eg).hom.app M =
      (projectionInverseImageIso R f k g efg).hom.app ((inverseImage p R).obj M) ≫
        (projectionInverseImageIso R p r k ek).hom.app M := by
  rw [projectionInverseImageIso_comp R p q r f g k ef eg ek efg M]
  simp only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

/-- A triangle whose top map is an identity is the identity comparison, up to
equality transport. -/
theorem projectionInverseImageIso_top_id (p : Y ⟶ X) {q : Y ⟶ X} {f : Y ⟶ Y}
    (e : f ≫ p = q) (e1 : f = 𝟙 Y) (eq : p = q) (M : ModuleSheaf X R) :
    (projectionInverseImageIso R p q f e).hom.app M =
      (inverseImageCongr R e1).hom.app ((inverseImage p R).obj M) ≫
        (inverseImageId R Y).hom.app ((inverseImage p R).obj M) ≫
        (inverseImageCongr R eq).hom.app M := by
  subst e1 eq
  rw [projectionInverseImageIso_id R p (𝟙 Y) e rfl M]
  simp

/-- A triangle whose base map is an identity is the inverse image of the identity
comparison, up to equality transport. -/
theorem projectionInverseImageIso_base_id {p : Y ⟶ Y} (f : Z ⟶ Y) {q : Z ⟶ Y}
    (e : f ≫ p = q) (e1 : p = 𝟙 Y) (eq : f = q) (M : ModuleSheaf Y R) :
    (projectionInverseImageIso R p q f e).hom.app M =
      (inverseImage f R).map ((inverseImageCongr R e1).hom.app M ≫
        (inverseImageId R Y).hom.app M) ≫ (inverseImageCongr R eq).hom.app M := by
  subst e1 eq
  have hi := congrArg (fun t => t.app M) (inverseImageComp_id_target R f)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hi
  dsimp only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app]
  rw [hi]
  simp

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Scheme.{u}}

/-- The comparison across a commuting square `p₂ ≫ f = f' ≫ p₁`: inverse image along `p₁`
and then `f'` is inverse image along `f` and then `p₂`. -/
def squareInverseImageMap (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (f : X₂ ⟶ X₁) (f' : Y₂ ⟶ Y₁)
    (s : p₂ ≫ f = f' ≫ p₁) (M : ModuleSheaf X₁ R) :
    (inverseImage f' R).obj ((inverseImage p₁ R).obj M) ⟶
      (inverseImage p₂ R).obj ((inverseImage f R).obj M) :=
  (projectionInverseImageIso R p₁ (f' ≫ p₁) f' rfl).hom.app M ≫
    (projectionInverseImageIso R f (f' ≫ p₁) p₂ s).inv.app M

/-- The square comparison is natural in the coefficient sheaf. -/
@[reassoc] theorem squareInverseImageMap_naturality (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (f : X₂ ⟶ X₁) (f' : Y₂ ⟶ Y₁) (s : p₂ ≫ f = f' ≫ p₁) {M N : ModuleSheaf X₁ R}
    (φ : M ⟶ N) :
    (inverseImage f' R).map ((inverseImage p₁ R).map φ) ≫
        squareInverseImageMap R p₁ p₂ f f' s N =
      squareInverseImageMap R p₁ p₂ f f' s M ≫
        (inverseImage p₂ R).map ((inverseImage f R).map φ) := by
  dsimp only [squareInverseImageMap]
  rw [← Category.assoc]
  erw [(projectionInverseImageIso R p₁ (f' ≫ p₁) f' rfl).hom.naturality φ]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact (projectionInverseImageIso R f (f' ≫ p₁) p₂ s).inv.naturality φ

/-- The square comparison of a square of identities is compatible with the identity
comparisons. -/
theorem squareInverseImageMap_id (p : Y₁ ⟶ X₁) (f : X₁ ⟶ X₁) (f' : Y₁ ⟶ Y₁)
    (s : p ≫ f = f' ≫ p) (e : f = 𝟙 X₁) (e' : f' = 𝟙 Y₁) (M : ModuleSheaf X₁ R) :
    squareInverseImageMap R p p f f' s M ≫
        (inverseImage p R).map ((inverseImageCongr R e).hom.app M ≫
          (inverseImageId R X₁).hom.app M) =
      (inverseImageCongr R e').hom.app ((inverseImage p R).obj M) ≫
        (inverseImageId R Y₁).hom.app ((inverseImage p R).obj M) := by
  have eq : p = f' ≫ p := by rw [e', Category.id_comp]
  have h2 := projectionInverseImageIso_base_id R p s e eq M
  have h3 : (projectionInverseImageIso R f (f' ≫ p) p s).inv.app M ≫
      (inverseImage p R).map ((inverseImageCongr R e).hom.app M ≫
        (inverseImageId R X₁).hom.app M) = (inverseImageCongr R eq).inv.app M := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, h2, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  dsimp only [squareInverseImageMap]
  rw [Category.assoc, h3, projectionInverseImageIso_top_id R p rfl e' eq M,
    Category.assoc, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

/-- A commuting square whose base map is an identity: its square comparison, followed by the
inverse image of the identity comparison, is the triangle comparison of the top map. -/
theorem squareInverseImageMap_base_id (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₁) (f : X₁ ⟶ X₁)
    (f' : Y₂ ⟶ Y₁) (s : p₂ ≫ f = f' ≫ p₁) (e : f = 𝟙 X₁) (e' : f' ≫ p₁ = p₂)
    (M : ModuleSheaf X₁ R) :
    squareInverseImageMap R p₁ p₂ f f' s M ≫
        (inverseImage p₂ R).map ((inverseImageCongr R e).hom.app M ≫
          (inverseImageId R X₁).hom.app M) =
      (projectionInverseImageIso R p₁ p₂ f' e').hom.app M := by
  have h2 := projectionInverseImageIso_base_id R p₂ s e e'.symm M
  have h3 : (projectionInverseImageIso R f (f' ≫ p₁) p₂ s).inv.app M ≫
      (inverseImage p₂ R).map ((inverseImageCongr R e).hom.app M ≫
        (inverseImageId R X₁).hom.app M) = (inverseImageCongr R e'.symm).inv.app M := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, h2, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  dsimp only [squareInverseImageMap]
  rw [Category.assoc, h3, inverseImageCongr_inv_app,
    projectionInverseImageIso_congr_comp R p₁ f' rfl e'.symm.symm M]

/-- Pasting two commuting squares: the square comparison of the composite square is the
composite of the square comparisons, through the composition comparisons on both sides. -/
theorem squareInverseImageMap_comp (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (p₃ : Y₃ ⟶ X₃)
    (fa : X₂ ⟶ X₁) (fb : X₃ ⟶ X₂) (fab : X₃ ⟶ X₁)
    (fa' : Y₂ ⟶ Y₁) (fb' : Y₃ ⟶ Y₂) (fab' : Y₃ ⟶ Y₁)
    (sa : p₂ ≫ fa = fa' ≫ p₁) (sb : p₃ ≫ fb = fb' ≫ p₂) (sab : p₃ ≫ fab = fab' ≫ p₁)
    (ec : fb ≫ fa = fab) (ec' : fb' ≫ fa' = fab') (M : ModuleSheaf X₁ R) :
    (projectionInverseImageIso R fa' fab' fb' ec').hom.app ((inverseImage p₁ R).obj M) ≫
        squareInverseImageMap R p₁ p₃ fab fab' sab M =
      (inverseImage fb' R).map (squareInverseImageMap R p₁ p₂ fa fa' sa M) ≫
        squareInverseImageMap R p₂ p₃ fb fb' sb ((inverseImage fa R).obj M) ≫
        (inverseImage p₃ R).map ((projectionInverseImageIso R fa fab fb ec).hom.app M) := by
  have eg : fb' ≫ fa' ≫ p₁ = fab' ≫ p₁ := by rw [← Category.assoc, ec']
  have ek : (fb' ≫ p₂) ≫ fa = fab' ≫ p₁ := by rw [Category.assoc, sa, ← Category.assoc, ec']
  have ek' : (p₃ ≫ fb) ≫ fa = fab' ≫ p₁ := by rw [Category.assoc, ec, sab]
  -- Step A: the top triangles.
  have hA := projectionInverseImageIso_paste R p₁ (fa' ≫ p₁) (fab' ≫ p₁) fa' fb' fab'
    rfl eg rfl ec' M
  -- Step B: the left triangles.
  have hB := projectionInverseImageIso_paste R fa (fa' ≫ p₁) (fab' ≫ p₁) p₂ fb'
    (fb' ≫ p₂) sa eg ek rfl M
  -- Step C: the bottom triangles.
  have hC := projectionInverseImageIso_paste R fa fab (fab' ≫ p₁) fb p₃ (p₃ ≫ fb)
    ec sab ek' rfl M
  -- The right triangle at `fb`.
  have hD := projectionInverseImageIso_congr_comp R fb p₃ (rfl : p₃ ≫ fb = p₃ ≫ fb) sb
    ((inverseImage fa R).obj M)
  have hE := projectionInverseImageIso_congr_top R fa sb.symm ek ek' M
  have hD' : (projectionInverseImageIso R fb (fb' ≫ p₂) p₃ sb).inv.app
        ((inverseImage fa R).obj M) ≫
      (projectionInverseImageIso R fb (p₃ ≫ fb) p₃ rfl).hom.app ((inverseImage fa R).obj M) =
      (inverseImageCongr R sb).inv.app ((inverseImage fa R).obj M) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, ← hD, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  dsimp only [squareInverseImageMap]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hA]
  simp only [Category.assoc]
  refine whisker_eq _ ?_
  rw [← cancel_epi ((inverseImage fb' R).map
    ((projectionInverseImageIso R fa (fa' ≫ p₁) p₂ sa).hom.app M))]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, hB]
  simp only [Category.assoc]
  refine whisker_eq _ ?_
  rw [← Iso.app_inv (projectionInverseImageIso R fab (fab' ≫ p₁) p₃ sab) M, Iso.comp_inv_eq,
    Iso.app_hom]
  simp only [Category.assoc]
  rw [hC, ← Category.assoc, hD', inverseImageCongr_inv_app, hE]

end Langlands.Geometry.EtaleInverseImage

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {J : Type v} [Category.{w} J]

/-- The composition comparison of a scheme diagram is a triangle comparison. -/
theorem diagramInverseImageComp_eq (R : Type u) [CommRing R] (T : J ⥤ Scheme.{u}ᵒᵖ)
    {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    diagramInverseImageComp R T a b =
      projectionInverseImageIso R (T.map a).unop (T.map (a ≫ b)).unop (T.map b).unop
        (congrArg Quiver.Hom.unop (T.map_comp a b)).symm := rfl

variable {S S' : J ⥤ Scheme.{u}ᵒᵖ} (R : Type u) [CommRing R] (π : S ⟶ S')

/-- The scheme map at a vertex given by a morphism of contravariant scheme diagrams. -/
abbrev diagramProjection (i : J) : (S'.obj i).unop ⟶ (S.obj i).unop := (π.app i).unop

/-- Naturality of a morphism of contravariant scheme diagrams is a commuting square of
scheme maps. -/
theorem diagramProjection_square {i j : J} (a : i ⟶ j) :
    diagramProjection π j ≫ (S.map a).unop = (S'.map a).unop ≫ diagramProjection π i :=
  congrArg Quiver.Hom.unop (π.naturality a)

namespace CoefficientDiagram

/-- The inverse image of a coefficient diagram on `S` along a morphism `π : S ⟶ S'` of
contravariant scheme diagrams: at each vertex the inverse image along the projection, with the
transition maps given by the square comparisons followed by the inverse images of the original
transition maps. -/
def pullback (D : CoefficientDiagram R S) : CoefficientDiagram R S' where
  obj i := (inverseImage (diagramProjection π i) R).obj (D.obj i)
  map {i j} a := squareInverseImageMap R (diagramProjection π i) (diagramProjection π j)
      (S.map a).unop (S'.map a).unop (diagramProjection_square π a) (D.obj i) ≫
    (inverseImage (diagramProjection π j) R).map (D.map a)
  map_id i := by
    have h := squareInverseImageMap_id R (diagramProjection π i) (S.map (𝟙 i)).unop
      (S'.map (𝟙 i)).unop (diagramProjection_square π (𝟙 i))
      (congrArg Quiver.Hom.unop (S.map_id i)) (congrArg Quiver.Hom.unop (S'.map_id i)) (D.obj i)
    rw [D.map_id]
    simpa only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app] using h
  map_comp {i j k} a b := by
    have h := squareInverseImageMap_comp R (diagramProjection π i) (diagramProjection π j)
      (diagramProjection π k) (S.map a).unop (S.map b).unop (S.map (a ≫ b)).unop
      (S'.map a).unop (S'.map b).unop (S'.map (a ≫ b)).unop (diagramProjection_square π a)
      (diagramProjection_square π b) (diagramProjection_square π (a ≫ b))
      (congrArg Quiver.Hom.unop (S.map_comp a b)).symm
      (congrArg Quiver.Hom.unop (S'.map_comp a b)).symm (D.obj i)
    have hD := D.map_comp a b
    rw [diagramInverseImageComp_eq] at hD
    rw [diagramInverseImageComp_eq, ← Category.assoc, h,
      (diagramInverseImage R S' b).map_comp]
    simp only [Category.assoc]
    rw [squareInverseImageMap_naturality_assoc,← (inverseImage (diagramProjection π k) R).map_comp,
      ← (inverseImage (diagramProjection π k) R).map_comp, hD]

/-- The vertices of the pulled-back diagram are inverse images of the original vertices. -/
@[simp] theorem pullback_obj (D : CoefficientDiagram R S) (i : J) :
    (pullback R π D).obj i = (inverseImage (diagramProjection π i) R).obj (D.obj i) := rfl

/-- The transitions of the pulled-back diagram. -/
theorem pullback_map (D : CoefficientDiagram R S) {i j : J} (a : i ⟶ j) :
    (pullback R π D).map a =
      squareInverseImageMap R (diagramProjection π i) (diagramProjection π j)
        (S.map a).unop (S'.map a).unop (diagramProjection_square π a) (D.obj i) ≫
      (inverseImage (diagramProjection π j) R).map (D.map a) := rfl

/-- Morphisms of coefficient diagrams pull back to morphisms by their inverse images. -/
def pullbackMap {D E : CoefficientDiagram R S} (α : D ⟶ E) :
    pullback R π D ⟶ pullback R π E where
  app i := (inverseImage (diagramProjection π i) R).map (α.app i)
  comm {i j} a := by
    change (squareInverseImageMap R _ _ _ _ _ (D.obj i) ≫ _) ≫ _ =
      _ ≫ squareInverseImageMap R _ _ _ _ _ (E.obj i) ≫ _
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, α.comm a,
      CategoryTheory.Functor.map_comp, ← squareInverseImageMap_naturality_assoc]

/-- Pullback along a morphism of scheme diagrams is a functor on coefficient diagrams. -/
def pullbackFunctor : CoefficientDiagram R S ⥤ CoefficientDiagram R S' where
  obj := pullback R π
  map := pullbackMap R π
  map_id D := by
    apply Hom.ext
    funext i
    exact (inverseImage (diagramProjection π i) R).map_id (D.obj i)
  map_comp α β := by
    apply Hom.ext
    funext i
    exact (inverseImage (diagramProjection π i) R).map_comp (α.app i) (β.app i)

end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram
