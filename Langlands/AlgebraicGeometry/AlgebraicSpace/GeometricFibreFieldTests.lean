import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismPointMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraically closed field tests for connected fibres -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}}

/-- The actual fibre map induced by a morphism of represented target tests. -/
def fibreSchemeTestMap {F G : Presheaf S} (f : F ⟶ G) {U V : Over S}
    (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ G) :
    Limits.pullback f ((schemeYoneda S).map k ≫ y) ⟶ Limits.pullback f y :=
  Limits.pullback.lift (Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ (schemeYoneda S).map k) (by
      rw [Category.assoc]
      exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem fibreSchemeTestMap_fst {F G : Presheaf S} (f : F ⟶ G) {U V : Over S}
    (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ G) :
    fibreSchemeTestMap f k y ≫ Limits.pullback.fst f y =
      Limits.pullback.fst f ((schemeYoneda S).map k ≫ y) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreSchemeTestMap_snd {F G : Presheaf S} (f : F ⟶ G) {U V : Over S}
    (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ G) :
    fibreSchemeTestMap f k y ≫ Limits.pullback.snd f y =
      Limits.pullback.snd f ((schemeYoneda S).map k ≫ y) ≫ (schemeYoneda S).map k :=
  Limits.pullback.lift_snd _ _ _

/-- The map between actual fibres is the base change of the represented test map. -/
theorem fibreSchemeTestMap_isPullback {F G : Presheaf S} (f : F ⟶ G) {U V : Over S}
    (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ G) :
    IsPullback (fibreSchemeTestMap f k y)
      (Limits.pullback.snd f ((schemeYoneda S).map k ≫ y))
      (Limits.pullback.snd f y) ((schemeYoneda S).map k) := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback f y)
  · rw [fibreSchemeTestMap_fst]
    exact IsPullback.of_hasPullback f ((schemeYoneda S).map k ≫ y)
  · exact fibreSchemeTestMap_snd f k y

/-- Surjectivity of a scheme test map passes to its actual fibre map. -/
theorem fibreSchemeTestMap_isSurjective {F G : Presheaf S} (f : F ⟶ G) {U V : Over S}
    (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ G) (hk : Surjective k.left) :
    IsSurjective (fibreSchemeTestMap f k y) :=
  MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (fibreSchemeTestMap_isPullback f k y).flip
    (SpaceProductPoints.isSurjective_map k hk)

/-- Maps between the fibre point spaces of an algebraic-space morphism are continuous. -/
theorem fibreSchemeTestMap_continuous {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U V : Over S} (k : U ⟶ V) (y : (schemeYoneda S).obj V ⟶ Y.presheaf) :
    Continuous[pointTopology _, pointTopology _] (Points.map (fibreSchemeTestMap (hom f) k y)) := by
  let y₀ : (schemeToSpace S).obj V ⟶ Y := homMk y
  obtain ⟨W, b, he, hs⟩ := (fibreProduct f y₀).property.2
  let e := FibreProduct.presheafIso f y₀
  exact Points.continuous_map_of_atlas _ (b ≫ e.hom) (he.comp_iso e) (hs.comp_iso e)

/-- Connectedness of a fibre descends from any extension of its field test. -/
theorem connectedSpace_fibre_of_field_extension {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {K L : Type u} [Field K] [Field L]
    {s : Spec (CommRingCat.of K) ⟶ S} {t : Spec (CommRingCat.of L) ⟶ S}
    (k : Over.mk t ⟶ Over.mk s)
    (y : (schemeYoneda S).obj (Over.mk s) ⟶ Y.presheaf)
    (hc : @ConnectedSpace (Points (Limits.pullback (hom f) ((schemeYoneda S).map k ≫ y)))
      (pointTopology _)) :
    @ConnectedSpace (Points (Limits.pullback (hom f) y)) (pointTopology _) := by
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map k ≫ y))
  let := pointTopology (Limits.pullback (hom f) y)
  let := hc
  have : Nonempty (Over.mk t).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of L)))
  have : Subsingleton (Over.mk s).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  have hk : Surjective k.left := ⟨Function.surjective_to_subsingleton _⟩
  exact (Points.surjective_map (fibreSchemeTestMap_isSurjective (hom f) k y hk)).connectedSpace
    (fibreSchemeTestMap_continuous f k y)

/-- In the published connected-fibre predicate it suffices to test algebraically
closed fields; nonemptiness is retained through the continuous surjective fibre map. -/
theorem hasGeometricallyConnectedFibres_iff_algClosed {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    HasGeometricallyConnectedFibres f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
        (y : (schemeYoneda S).obj (Over.mk s) ⟶ Y.presheaf),
        @ConnectedSpace (Points (Limits.pullback (hom f) y)) (pointTopology _) := by
  constructor
  · intro hf K _ _ s y
    exact hf K s y
  · intro hf K _ s y
    let e : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    let k : Over.mk (e ≫ s) ⟶ Over.mk s := Over.homMk e rfl
    exact connectedSpace_fibre_of_field_extension f k y
      (hf (AlgebraicClosure K) (e ≫ s) ((schemeYoneda S).map k ≫ y))

end Langlands.AlgebraicGeometry.AlgebraicSpace
