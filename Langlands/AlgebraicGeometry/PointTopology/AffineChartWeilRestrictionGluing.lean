import Langlands.AlgebraicGeometry.PointTopology.AffineOpenEmbeddingProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionPullbacks
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Gluing the actual affine-chart Weil restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R)))

@[simp]
theorem openOverHomOfLE_id (U : X.left.Opens) :
    openOverHomOfLE R X (le_refl U) = 𝟙 (openOver R X U) := by
  apply Over.OverMorphism.ext
  exact X.left.homOfLE_rfl U

@[simp]
theorem openOverHomOfLE_comp {U V W : X.left.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    openOverHomOfLE R X (hUV.trans hVW) =
      openOverHomOfLE R X hUV ≫ openOverHomOfLE R X hVW := by
  apply Over.OverMorphism.ext
  exact (X.left.homOfLE_homOfLE hUV hVW).symm

instance openOverHomOfLE_isOpenImmersion {U V : X.left.Opens} (h : U ≤ V) :
    IsOpenImmersion (openOverHomOfLE R X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

instance affineOpenOver_isAffine (U : X.left.affineOpens) :
    IsAffine (openOver R X U.val).left := U.property

instance openOver_locallyOfFiniteType [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (openOver R X U).hom := by
  change LocallyOfFiniteType (U.ι ≫ X.hom)
  infer_instance

/-- Two affine opens contained in one affine open have affine intersection,
without a separatedness hypothesis on the ambient scheme. -/
theorem isAffineOpen_inf_of_common_affine (U V K : X.left.affineOpens)
    (hU : U ≤ K) (hV : V ≤ K) : IsAffineOpen (U.val ⊓ V.val) := by
  let : IsAffine U.val := U.property
  let : IsAffine V.val := V.property
  let : IsAffine K.val := K.property
  exact IsAffine.of_isIso (isPullback_opens_inf_le hU hV).isoPullback.hom

/-- The ordinary intersection square is also cartesian over the original base. -/
theorem openOverHomOfLE_isPullback {U V K : X.left.Opens}
    (hU : U ≤ K) (hV : V ≤ K) :
    IsPullback (openOverHomOfLE R X (inf_le_left : U ⊓ V ≤ U))
      (openOverHomOfLE R X (inf_le_right : U ⊓ V ≤ V))
      (openOverHomOfLE R X hU) (openOverHomOfLE R X hV) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of R)))
  exact isPullback_opens_inf_le hU hV

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The diagram of actual affine Weil restrictions of all affine opens. -/
def affineChartWeilRestrictionDiagram : Y.left.affineOpens ⥤ Scheme.{u} where
  obj U := (affineWeilRestriction A B (openOver B Y U.val)).left
  map {U V} f := (affineWeilRestrictionMap A B
    (openOverHomOfLE B Y (leOfHom f))).left
  map_id U := by
    change (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y (le_refl U.val))).left = _
    rw [openOverHomOfLE_id, affineWeilRestrictionMap_id]
    rfl
  map_comp {U V W} f g := by
    change (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y ((leOfHom f).trans (leOfHom g)))).left = _
    rw [openOverHomOfLE_comp B Y (leOfHom f) (leOfHom g),
      affineWeilRestrictionMap_comp]
    rfl

instance affineChartWeilRestrictionDiagram_map_isOpenImmersion
    {U V : Y.left.affineOpens} (f : U ⟶ V) :
    IsOpenImmersion ((affineChartWeilRestrictionDiagram A B Y).map f) :=
  affineWeilRestrictionMap_isOpenImmersion A B
    (openOverHomOfLE B Y (leOfHom f))

/-- Equal-image chart points lift through the restriction of an actual affine
intersection inside their common upper chart. -/
instance affineChartWeilRestrictionDiagram_isLocallyDirected :
    (affineChartWeilRestrictionDiagram A B Y ⋙ Scheme.forget).IsLocallyDirected where
  cond {U V K} f g x y hxy := by
    let W : Y.left.affineOpens :=
      ⟨U.val ⊓ V.val, isAffineOpen_inf_of_common_affine B Y U V K (leOfHom f) (leOfHom g)⟩
    let : IsAffine (openOver B Y W.val).left := W.property
    have hWU : W ≤ U := (inf_le_left : U.val ⊓ V.val ≤ U.val)
    have hWV : W ≤ V := (inf_le_right : U.val ⊓ V.val ≤ V.val)
    have h := affineWeilRestrictionMap_isPullback A B
      (openOverHomOfLE B Y (inf_le_left : W.val ≤ U.val))
      (openOverHomOfLE B Y (inf_le_right : W.val ≤ V.val))
      (openOverHomOfLE B Y (leOfHom f))
      (openOverHomOfLE B Y (leOfHom g))
      (openOverHomOfLE_isPullback B Y (leOfHom f) (leOfHom g))
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
      (h.map (Over.forget (Spec (CommRingCat.of A)))) x y hxy
    exact ⟨W, homOfLE hWU, homOfLE hWV, z, hz₁, hz₂⟩

/-- Compatible chart structure maps to the smaller affine base. -/
def affineChartWeilRestrictionBaseCocone :
    Cocone (affineChartWeilRestrictionDiagram A B Y) where
  pt := Spec (CommRingCat.of A)
  ι.app U := (affineWeilRestriction A B (openOver B Y U.val)).hom
  ι.naturality {_U _V} f := Over.w (affineWeilRestrictionMap A B
    (openOverHomOfLE B Y (leOfHom f)))

/-- The actual scheme obtained by gluing all affine-chart Weil restrictions,
with its structure morphism to `Spec A`. Representability is a further result. -/
def affineChartWeilRestriction : Over (Spec (CommRingCat.of A)) :=
  Over.mk (colimit.desc (affineChartWeilRestrictionDiagram A B Y)
    (affineChartWeilRestrictionBaseCocone A B Y))

/-- The chart maps are genuine morphisms over the smaller base. -/
def affineChartWeilRestrictionι (U : Y.left.affineOpens) :
    affineWeilRestriction A B (openOver B Y U.val) ⟶ affineChartWeilRestriction A B Y :=
  Over.homMk (colimit.ι (affineChartWeilRestrictionDiagram A B Y) U)
    (colimit.ι_desc (affineChartWeilRestrictionBaseCocone A B Y) U)

/-- The glued scheme is covered by the actual affine Weil-restriction charts. -/
def affineChartWeilRestrictionOpenCover : (affineChartWeilRestriction A B Y).left.OpenCover :=
  Scheme.IsLocallyDirected.openCover (affineChartWeilRestrictionDiagram A B Y)

instance affineChartWeilRestrictionι_isOpenImmersion (U : Y.left.affineOpens) :
    IsOpenImmersion (affineChartWeilRestrictionι A B Y U).left :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (affineChartWeilRestrictionDiagram A B Y) U))

@[simp]
theorem affineChartWeilRestrictionι_naturality {U V : Y.left.affineOpens} (h : U ≤ V) :
    affineWeilRestrictionMap A B (openOverHomOfLE B Y h) ≫
        affineChartWeilRestrictionι A B Y V = affineChartWeilRestrictionι A B Y U := by
  apply Over.OverMorphism.ext
  exact colimit.w (affineChartWeilRestrictionDiagram A B Y) (homOfLE h)

/-- Every point of the actual glued scheme is in one of its affine charts. -/
theorem affineChartWeilRestrictionι_jointly_surjective
    (x : (affineChartWeilRestriction A B Y).left) :
    ∃ (U : Y.left.affineOpens) (p : (affineWeilRestriction A B (openOver B Y U.val)).left),
      (affineChartWeilRestrictionι A B Y U).left p = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (affineChartWeilRestrictionDiagram A B Y) x

/-- Chart points are identified exactly when they have a common affine-open
refinement, with the existing coordinate maps as refinement maps. -/
theorem affineChartWeilRestrictionι_eq_iff {U V : Y.left.affineOpens}
    (p : (affineWeilRestriction A B (openOver B Y U.val)).left)
    (q : (affineWeilRestriction A B (openOver B Y V.val)).left) :
    (affineChartWeilRestrictionι A B Y U).left p =
        (affineChartWeilRestrictionι A B Y V).left q ↔
      ∃ (W : Y.left.affineOpens) (hU : W ≤ U) (hV : W ≤ V)
        (r : (affineWeilRestriction A B (openOver B Y W.val)).left),
        (affineWeilRestrictionMap A B (openOverHomOfLE B Y hU)).left r = p ∧
        (affineWeilRestrictionMap A B (openOverHomOfLE B Y hV)).left r = q := by
  constructor
  · intro h
    obtain ⟨W, f, g, r, hr₁, hr₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (affineChartWeilRestrictionDiagram A B Y)).mp h
    exact ⟨W, leOfHom f, leOfHom g, r, hr₁, hr₂⟩
  · rintro ⟨W, hU, hV, r, hr₁, hr₂⟩
    exact (Scheme.IsLocallyDirected.ι_eq_ι_iff (affineChartWeilRestrictionDiagram A B Y)).mpr
      ⟨W, homOfLE hU, homOfLE hV, r, hr₁, hr₂⟩

end Langlands.AlgebraicGeometry.PointTopology
