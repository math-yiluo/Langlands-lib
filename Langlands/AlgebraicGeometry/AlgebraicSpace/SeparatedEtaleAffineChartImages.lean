import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImageDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Represented images of affine structurally etale charts -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages

open EtaleImageSaturation CompactLocalImage

variable {S : Scheme.{u}}

/-- The graph of an etale chart over an etale scheme composite is open. -/
theorem graph_isOpenImmersion
    {F G : Presheaf S} {B T : Over S} (e : B ⟶ T) [Etale e.left]
    {π : G ⟶ F} {p : G ⟶ (schemeYoneda S).obj B}
    {f : F ⟶ (schemeYoneda S).obj T}
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj B ⟶ F) (ha : IsEtale a)
    (hw : a ≫ f = (schemeYoneda S).map e)
    (b : (schemeYoneda S).obj B ⟶ G)
    (hbπ : b ≫ π = a) (hbp : b ≫ p = 𝟙 _) : IsOpenImmersion b := by
  have hcompat : ((schemeYoneda S).map (left e) ≫ a) ≫ f =
      (schemeYoneda S).map (right e) ≫ (schemeYoneda S).map e := by
    rw [Category.assoc, hw, ← Functor.map_comp, ← Functor.map_comp,
      (relation_isPullback e).w]
  let c := sq.lift ((schemeYoneda S).map (left e) ≫ a)
    ((schemeYoneda S).map (right e)) hcompat
  have hcπ : c ≫ π = (schemeYoneda S).map (left e) ≫ a := sq.lift_fst _ _ _
  have hcp : c ≫ p = (schemeYoneda S).map (right e) := sq.lift_snd _ _ _
  have houter : IsPullback ((schemeYoneda S).map (left e)) (c ≫ p)
      (a ≫ f) ((schemeYoneda S).map e) := by
    rw [hcp, hw]
    exact (relation_isPullback e).map (schemeYoneda S)
  have hc : IsPullback ((schemeYoneda S).map (left e)) c a π :=
    houter.of_bot hcπ.symm sq
  have hce : IsEtale c := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
      (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
    exact MorphismProperty.of_isPullback
      (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
        (schemeYoneda S)) hc ha
  have hdiag : (schemeYoneda S).map (diagonal e) ≫ c = b := by
    apply sq.hom_ext
    · rw [Category.assoc, hcπ, ← Functor.map_comp_assoc, diagonal_left,
        (schemeYoneda S).map_id B, Category.id_comp, hbπ]
    · rw [Category.assoc, hcp, ← Functor.map_comp, diagonal_right,
        (schemeYoneda S).map_id B, hbp]
  have hbe : IsEtale b := by
    rw [← hdiag]
    exact (isEtale_map (diagonal e) (by
      change Etale (pullback.diagonal e.left)
      infer_instance)).comp hce
  let : Mono b := mono_of_mono_fac hbp
  refine ⟨hbe.rep, ?_⟩
  intro U V g fst snd hsq
  let : Etale snd.left := hbe.property g fst snd hsq
  let : Mono snd := (schemeYoneda S).mono_of_mono_map hsq.mono_snd_of_mono
  let : Mono snd.left := inferInstance
  exact _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono snd.left

/-- An affine etale chart with etale affine structural composite has compact
represented local image in a closed-diagonal sheaf. -/
theorem of_affine_chart
    {F : FppfSheaf S} {B T : Over S} [IsAffine B.left] [IsAffine T.left]
    (hF : IsClosedImmersion (diag F.obj))
    (f : F.obj ⟶ (schemeYoneda S).obj T)
    (a : (schemeYoneda S).obj B ⟶ F.obj) (ha : IsEtale a)
    (e : B ⟶ T) [Etale e.left]
    (hw : a ≫ f = (schemeYoneda S).map e) :
    HasCompactRepresentation ((Subfunctor.range a).sheafify (fppfTopology S)) := by
  let fS : F ⟶ (schemeSheaf S).obj T := ObjectProperty.homMk f
  let G : FppfSheaf S := Limits.pullback fS ((schemeSheaf S).map e)
  let π : G.obj ⟶ F.obj := (pullback.fst fS ((schemeSheaf S).map e)).hom
  let p : G.obj ⟶ (schemeYoneda S).obj B :=
    (pullback.snd fS ((schemeSheaf S).map e)).hom
  have sq : IsPullback π p f ((schemeYoneda S).map e) :=
    (IsPullback.of_hasPullback fS ((schemeSheaf S).map e)).map
      (sheafToPresheaf (fppfTopology S) (Type (u + 1)))
  let b := sq.lift a (𝟙 _) (by simpa using hw)
  have hbπ : b ≫ π = a := sq.lift_fst _ _ _
  have hbp : b ≫ p = 𝟙 _ := sq.lift_snd _ _ _
  have hb := graph_isOpenImmersion e sq a ha hw b hbπ hbp
  let : Etale (𝟙 B : B ⟶ B).left := inferInstanceAs (Etale (𝟙 B.left))
  have h := SeparatedEtaleImageDescent.of_affine_etale e hF sq b hb (𝟙 B)
    (by simpa using hbp)
  rwa [hbπ] at h

end Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleImages
