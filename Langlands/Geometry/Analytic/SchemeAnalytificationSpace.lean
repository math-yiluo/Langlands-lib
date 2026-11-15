import Langlands.Geometry.Analytic.AffineSchemeAnalytification
import Langlands.Geometry.Analytic.AffineAnalytificationMap

/-! # The glued analytification space of a scheme locally of finite type -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

section Algebraic

variable {K : Type u} [CommRing K]

/-- The `K`-algebra map of actual global-section algebras induced by a morphism of
schemes over `Spec K`. -/
def coordinateMap {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)}
    {fY : Y ⟶ Spec (CommRingCat.of K)} (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    CoordinateRing fY →ₐ[K] CoordinateRing fX where
  toRingHom := g.appTop.hom
  commutes' k := by
    change g.appTop (fY.appTop _) = fX.appTop _
    rw [← hg, Scheme.Hom.comp_appTop]
    rfl

@[simp] theorem coordinateMap_apply {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)}
    {fY : Y ⟶ Spec (CommRingCat.of K)} (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (a : CoordinateRing fY) : coordinateMap g hg a = g.appTop a := rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The structure morphism of an affine open subscheme over `Spec K`. -/
abbrev structureMap (U : X.affineOpens) : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of K) :=
  (U : X.Opens).ι ≫ f

/-- Restriction of actual global sections from an affine open to a smaller one. -/
def restriction {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    CoordinateRing (structureMap f U) →ₐ[K] CoordinateRing (structureMap f V) :=
  coordinateMap (X.homOfLE h) (by
    rw [structureMap, structureMap, ← Category.assoc, Scheme.homOfLE_ι])

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The chosen finite polynomial presentation of the global sections of an affine open. -/
abbrev chartPresentation (U : X.affineOpens) :
    FinitePolynomialPresentation K (CoordinateRing (structureMap f U)) :=
  presentation (structureMap f U)

/-- The polynomial-locus analytification of an affine open subscheme. -/
abbrev LocalSpace (U : X.affineOpens) : Type u :=
  AffineAnalytification.Space K (chartPresentation K f U)

/-- The continuous map of analytifications induced by an inclusion of affine opens. -/
def localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    C(LocalSpace K f V, LocalSpace K f U) :=
  AffineAnalytification.baseMap K (chartPresentation K f U) (chartPresentation K f V)
    (restriction f h)

/-- The gluing relation: a point of the analytification of `V` is identified with its
image in the analytification of every affine open `U` containing `V`. -/
inductive Glue : (Σ U : X.affineOpens, LocalSpace K f U) →
    (Σ U : X.affineOpens, LocalSpace K f U) → Prop
  | mk {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) (y : LocalSpace K f V) :
      Glue ⟨V, y⟩ ⟨U, localMap K f h y⟩

/-- The analytification space of `X`: the quotient of the disjoint union of the
analytifications of all affine opens by the gluing relation, with the quotient
topology of the sigma topology. -/
def Space : Type u := Quot (Glue K f)

instance : TopologicalSpace (Space K f) :=
  inferInstanceAs (TopologicalSpace (Quot (Glue K f)))

/-- The canonical map from the analytification of an affine open. -/
def ι (U : X.affineOpens) : C(LocalSpace K f U, Space K f) :=
  ⟨fun y => Quot.mk (Glue K f) ⟨U, y⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

theorem ι_apply (U : X.affineOpens) (y : LocalSpace K f U) :
    ι K f U y = Quot.mk (Glue K f) ⟨U, y⟩ := rfl

/-- The canonical maps are compatible with the maps induced by inclusions. -/
theorem ι_localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) (y : LocalSpace K f V) :
    ι K f U (localMap K f h y) = ι K f V y :=
  (Quot.sound (Glue.mk h y)).symm

/-- Every point of the glued space comes from some affine open. -/
theorem exists_ι (z : Space K f) : ∃ (U : X.affineOpens) (y : LocalSpace K f U), ι K f U y = z := by
  induction z using Quot.ind with
  | mk p => exact ⟨p.1, p.2, rfl⟩

/-- The quotient map from the disjoint union of the affine analytifications. -/
theorem isQuotientMap_mk : IsQuotientMap (Quot.mk (Glue K f)) := isQuotientMap_quot_mk

/-- A set is open in the glued space exactly when its preimage in the analytification
of every affine open is open. -/
theorem isOpen_iff (s : Set (Space K f)) :
    IsOpen s ↔ ∀ U : X.affineOpens, IsOpen (ι K f U ⁻¹' s) :=
  ((isQuotientMap_mk K f).isOpen_preimage (s := s)).symm.trans isOpen_sigma_iff

/-- The universal property of the glued space: compatible continuous maps out of
the affine analytifications descend uniquely. -/
def desc {T : Type*} [TopologicalSpace T] (g : ∀ U : X.affineOpens, C(LocalSpace K f U, T))
    (hg : ∀ {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) (y : LocalSpace K f V),
      g U (localMap K f h y) = g V y) : C(Space K f, T) :=
  ⟨Quot.lift (fun p => g p.1 p.2) (by
      rintro _ _ ⟨h, y⟩
      exact (hg h y).symm),
    continuous_quot_lift _ (continuous_sigma fun U => (g U).continuous)⟩

@[simp] theorem desc_ι {T : Type*} [TopologicalSpace T]
    (g : ∀ U : X.affineOpens, C(LocalSpace K f U, T))
    (hg : ∀ {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) (y : LocalSpace K f V),
      g U (localMap K f h y) = g V y) (U : X.affineOpens) (y : LocalSpace K f U) :
    desc K f g hg (ι K f U y) = g U y := rfl

theorem desc_unique {T : Type*} [TopologicalSpace T] {φ ψ : C(Space K f, T)}
    (h : ∀ (U : X.affineOpens) (y : LocalSpace K f U), φ (ι K f U y) = ψ (ι K f U y)) :
    φ = ψ := by
  ext z
  obtain ⟨U, y, rfl⟩ := exists_ι K f z
  exact h U y

end Normed

end Langlands.Analytic.SchemeAnalytification
