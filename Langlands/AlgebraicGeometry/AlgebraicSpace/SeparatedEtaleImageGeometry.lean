import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleImageSaturation
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompactLocalImage
import Langlands.AlgebraicGeometry.AlgebraicSpace.PullbackDiagonals
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentableTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionDiagonal
import Langlands.AlgebraicGeometry.FiniteEtaleSourceUnramified
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite

/-! # Geometry of represented etale images in separated sheaves -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages

variable {S : Scheme.{u}}

local instance : (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ _

local instance : MorphismProperty.IsStableUnderComposition
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})).toIsStableUnderComposition

local instance : (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)

local instance : (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).IsMultiplicative where
  id_mem X := inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion (𝟙 X.left))

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- Pulling back a separated sheaf along an affine scheme preserves its closed diagonal. -/
theorem closed_diagonal_of_affine_pullback
    {F G : Presheaf S} {B T : Over S} [IsAffine B.left]
    {π : G ⟶ F} {p : G ⟶ (schemeYoneda S).obj B}
    {f : F ⟶ (schemeYoneda S).obj T} {e : B ⟶ T}
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (hF : IsClosedImmersion (diag F)) : IsClosedImmersion (diag G) := by
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
      (schemeYoneda S)
  let : P.IsMultiplicative := by dsimp [P]; infer_instance
  have hB : P (diag ((schemeYoneda S).obj B)) :=
    relative_diag_schemeYoneda @_root_.AlgebraicGeometry.IsClosedImmersion B inferInstance
  have h := PullbackDiagonals.pullback P f ((schemeYoneda S).map e) hF hB
  exact (MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk sq.isoPullback (Limits.prod.mapIso sq.isoPullback sq.isoPullback)
      (by simp))).mpr h

/-- A represented local image retains its etale source chart and is separated and
etale over the represented base when the original composite is etale. -/
theorem represented_image_geometry
    {G : Presheaf S} {D B W : Over S} [IsAffine D.left] [IsAffine B.left]
    (hG : IsClosedImmersion (diag G))
    (c : (schemeYoneda S).obj D ⟶ G) (hc : IsEtale c)
    (p : G ⟶ (schemeYoneda S).obj B) (w : D ⟶ B)
    (hw : c ≫ p = (schemeYoneda S).map w) [Etale w.left]
    (i : (schemeYoneda S).obj W ≅
      ((Subfunctor.range c).sheafify (fppfTopology S)).toFunctor) :
    ∃ (q : W ⟶ B) (d : D ⟶ W),
      (schemeYoneda S).map q =
        i.hom ≫ ((Subfunctor.range c).sheafify (fppfTopology S)).ι ≫ p ∧
      (schemeYoneda S).map d ≫ i.hom =
        Subfunctor.toRangeSheafify (fppfTopology S) c ∧
      d ≫ q = w ∧ _root_.AlgebraicGeometry.IsSeparated q.left ∧
        Etale d.left ∧ Surjective d.left ∧ Etale q.left := by
  let A := (Subfunctor.range c).sheafify (fppfTopology S)
  let a := Subfunctor.toRangeSheafify (fppfTopology S) c
  let q : W ⟶ B := (schemeYoneda S).preimage (i.hom ≫ A.ι ≫ p)
  let d : D ⟶ W := (schemeYoneda S).preimage (a ≫ i.inv)
  have hq : (schemeYoneda S).map q = i.hom ≫ A.ι ≫ p :=
    (schemeYoneda S).map_preimage _
  have hd : (schemeYoneda S).map d ≫ i.hom = a := by
    dsimp [d]
    rw [Functor.map_preimage]
    simp
  have hsq : IsPullback (𝟙 ((schemeYoneda S).obj D))
      ((schemeYoneda S).map d) a i.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hd.symm⟩
  have hde : Etale d.left :=
    (OpenSubfunctorImages.toRangeSheafify_isEtale c hc).projection
      i.hom (𝟙 _) d hsq
  have hds : Surjective d.left :=
    (OpenSubfunctorImages.toRangeSheafify_isSurjective c hc).projection
      i.hom (𝟙 _) d hsq
  have hdq : d ≫ q = w := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, hq, ← Category.assoc, hd, ← Category.assoc]
    have ha : a ≫ A.ι = c := by ext T x; rfl
    rw [ha, hw]
  let P := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)).relative
      (schemeYoneda S)
  let : P.IsMultiplicative := by dsimp [P]; infer_instance
  have hW : P (diag ((schemeYoneda S).obj W)) :=
    PullbackDiagonals.of_mono P (i.hom ≫ A.ι) hG
  have hsW : _root_.AlgebraicGeometry.IsSeparated W.hom :=
    isSeparated_of_representableBy
      ((Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ W).symm (Iso.refl _)) hW
  have hqs : _root_.AlgebraicGeometry.IsSeparated q.left := by
    have : _root_.AlgebraicGeometry.IsSeparated (q.left ≫ B.hom) := by
      rw [Over.w q]
      exact hsW
    exact _root_.AlgebraicGeometry.IsSeparated.of_comp q.left B.hom
  let : _root_.AlgebraicGeometry.IsSeparated q.left := hqs
  let : W.left.IsSeparated := ⟨by
    rw [← terminal.comp_from q.left]
    infer_instance⟩
  let : Etale d.left := hde
  let : Surjective d.left := hds
  let : Etale (d.left ≫ q.left) := by
    change Etale (d ≫ q).left
    rw [hdq]
    infer_instance
  let : Smooth q.left := smoothEtaleSourceDescent D.left W.left B.left d.left q.left
    hde hds inferInstance
  let : FormallyUnramified q.left := formallyUnramified_of_surjective_etale_comp d.left q.left
  have hqe : Etale q.left := Etale.of_formallyUnramified_of_flat q.left
  exact ⟨q, d, hq, hd, hdq, hqs, hde, hds, hqe⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages
