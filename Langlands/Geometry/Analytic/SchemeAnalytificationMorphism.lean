import Langlands.Geometry.Analytic.SchemeAnalytificationSpace

/-! # Analytifications of morphisms of schemes: the local maps and the compatibility predicate -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

section Algebraic

variable {K : Type u} [CommRing K] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of K)} {f' : Y ⟶ Spec (CommRingCat.of K)}

/-- For affine opens `U` of `X` and `V` of `Y` with `g(U) ⊆ V`, the `K`-algebra map
`Γ(V) → Γ(U)` of actual global sections induced by the restriction of `g`. -/
def openCoordinateMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) :
    CoordinateRing (structureMap f' V) →ₐ[K] CoordinateRing (structureMap f U) :=
  coordinateMap (g.resLE (V : Y.Opens) (U : X.Opens) h) (by
    rw [structureMap, structureMap, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hg])

theorem openCoordinateMap_apply (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens}
    {V : Y.affineOpens} (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (a : CoordinateRing (structureMap f' V)) :
    openCoordinateMap g hg h a = (g.resLE (V : Y.Opens) (U : X.Opens) h).appTop a :=
  rfl

/-- For the identity morphism, the induced map is the restriction of sections. -/
theorem openCoordinateMap_id {U V : X.affineOpens} (h : (U : X.Opens) ≤ (V : X.Opens)) :
    openCoordinateMap (f := f) (𝟙 X) (Category.id_comp f) (U := U) (V := V) h =
      restriction f h := by
  apply AlgHom.ext
  intro a
  exact congrArg (fun φ : ((U : X.Opens) : Scheme.{u}) ⟶ ((V : X.Opens) : Scheme.{u}) => φ.appTop a)
    (Scheme.Hom.resLE_id h)

/-- The induced maps are compatible with composition of morphisms. -/
theorem openCoordinateMap_comp {Z : Scheme.{u}} {f'' : Z ⟶ Spec (CommRingCat.of K)}
    (g : X ⟶ Y) (hg : g ≫ f' = f) (g' : Y ⟶ Z) (hg' : g' ≫ f'' = f')
    {U : X.affineOpens} {V : Y.affineOpens} {W : Z.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) (h' : (V : Y.Opens) ≤ g' ⁻¹ᵁ (W : Z.Opens))
    (h'' : (U : X.Opens) ≤ (g ≫ g') ⁻¹ᵁ (W : Z.Opens)) :
    openCoordinateMap (g ≫ g') (by rw [Category.assoc, hg', hg]) h'' =
      (openCoordinateMap g hg h).comp (openCoordinateMap g' hg' h') := by
  apply AlgHom.ext
  intro a
  have e : g.resLE (V : Y.Opens) (U : X.Opens) h ≫ g'.resLE (W : Z.Opens) (V : Y.Opens) h' =
      (g ≫ g').resLE (W : Z.Opens) (U : X.Opens) h'' :=
    Scheme.Hom.resLE_comp_resLE g h g' h'
  rw [AlgHom.comp_apply, openCoordinateMap_apply, openCoordinateMap_apply,
    openCoordinateMap_apply, ← e, Scheme.Hom.comp_appTop]
  exact CommRingCat.comp_apply _ _ _

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']

/-- For affine opens `U` of `X` and `V` of `Y` with `g(U) ⊆ V`, the continuous map of
affine analytifications `Uᵃⁿ → Vᵃⁿ` induced by `g`. -/
def morphismLocalMap (g : X ⟶ Y) (hg : g ≫ f' = f) {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) : C(LocalSpace K f U, LocalSpace K f' V) :=
  AffineAnalytification.baseMap K (chartPresentation K f' V) (chartPresentation K f U)
    (openCoordinateMap g hg h)

/-- A continuous map of glued analytifications is an analytification of `g` when, for
every affine open `U` of `X` and every affine open `V` of `Y` with `g(U) ⊆ V`, it sends
the image of a point `y` of `Uᵃⁿ` to the image of the point `morphismLocalMap y` of
`Vᵃⁿ`. -/
def IsAnalytificationMap (g : X ⟶ Y) (hg : g ≫ f' = f) (F : C(Space K f, Space K f')) :
    Prop :=
  ∀ (U : X.affineOpens) (V : Y.affineOpens) (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (y : LocalSpace K f U), F (ι K f U y) = ι K f' V (morphismLocalMap K f f' g hg h y)

/-- For the identity morphism, the local maps are the restriction maps of the glued
space. -/
theorem morphismLocalMap_id {U V : X.affineOpens} (h : (U : X.Opens) ≤ (V : X.Opens)) :
    morphismLocalMap K f f (𝟙 X) (Category.id_comp f) (U := U) (V := V) h = localMap K f h := by
  unfold morphismLocalMap localMap
  rw [openCoordinateMap_id]

/-- The identity map of the glued space is an analytification of the identity morphism. -/
theorem isAnalytificationMap_id :
    IsAnalytificationMap K f f (𝟙 X) (Category.id_comp f) (ContinuousMap.id (Space K f)) := by
  intro U V h y
  have h' : (U : X.Opens) ≤ (V : X.Opens) := h
  exact (ι_localMap K f h' y).symm.trans
    (congrArg (fun φ : C(LocalSpace K f U, LocalSpace K f V) => ι K f V (φ y))
      (morphismLocalMap_id K f h').symm)

/-- Two analytifications of the same morphism agree on the image of the analytification
of every affine open whose image lies in an affine open. -/
theorem IsAnalytificationMap.apply_eq {g : X ⟶ Y} {hg : g ≫ f' = f}
    {F G : C(Space K f, Space K f')} (hF : IsAnalytificationMap K f f' g hg F)
    (hG : IsAnalytificationMap K f f' g hg G) {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) (y : LocalSpace K f U) :
    F (ι K f U y) = G (ι K f U y) := by
  rw [hF U V h y, hG U V h y]

end Normed

end Langlands.Analytic.SchemeAnalytification
