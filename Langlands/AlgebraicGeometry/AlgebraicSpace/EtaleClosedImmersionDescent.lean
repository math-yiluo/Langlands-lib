import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Closedness of immersions checked on an etale atlas -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A preimmersion is closed if its pullback along a quotient map is closed. -/
theorem isClosedImmersion_of_quotient_pullback
    {Z T V : Scheme.{u}} (i : Z ⟶ T) (p : V ⟶ T) [IsPreimmersion i]
    (hp : Topology.IsQuotientMap p)
    [_root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd i p)] :
    _root_.AlgebraicGeometry.IsClosedImmersion i := by
  apply _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion
  apply hp.isCoinducing.isClosed_preimage.mp
  rw [← Scheme.Pullback.range_snd]
  exact (pullback.snd i p).isClosedEmbedding.isClosed_range

/-- Closedness descends through any surjective etale pullback square, provided
the original morphism is a preimmersion. -/
theorem isClosedImmersion_of_etale_surjective_square
    {W Z V T : Scheme.{u}} {r : W ⟶ Z} {j : W ⟶ V} {i : Z ⟶ T} {p : V ⟶ T}
    (h : IsPullback r j i p) [IsPreimmersion i] [Etale p] [Surjective p]
    [_root_.AlgebraicGeometry.IsClosedImmersion j] :
    _root_.AlgebraicGeometry.IsClosedImmersion i := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd i p) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact isClosedImmersion_of_quotient_pullback i p
    (p.isOpenMap.isQuotientMap p.continuous p.surjective)

/-- The actual open complement obtained by checking an immersed image after a
surjective etale base change. -/
def immersionComplementOfEtalePullback
    {Z T V : Scheme.{u}} (i : Z ⟶ T) (p : V ⟶ T) [IsPreimmersion i]
    [Etale p] [Surjective p]
    [_root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd i p)] : T.Opens :=
  have := isClosedImmersion_of_quotient_pullback i p
    (p.isOpenMap.isQuotientMap p.continuous p.surjective)
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[simp]
lemma mem_immersionComplementOfEtalePullback
    {Z T V : Scheme.{u}} (i : Z ⟶ T) (p : V ⟶ T) [IsPreimmersion i]
    [Etale p] [Surjective p]
    [_root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd i p)] (t : T) :
    t ∈ immersionComplementOfEtalePullback i p ↔ t ∉ Set.range i := Iff.rfl

/-- A representable immersion of presheaves is closed once its represented
pullback to one surjective etale atlas is closed. -/
theorem isClosedImmersion_of_etale_atlas
    {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage @IsImmersion.{u} (Over.forget S)).relative
      (schemeYoneda S) f)
    {U : Over S} (a : (schemeYoneda S).obj U ⟶ G)
    (ha : IsEtale a) (hs : IsSurjective a)
    (hc : _root_.AlgebraicGeometry.IsClosedImmersion (hf.rep.snd a).left) :
    IsClosedImmersion f := by
  let Y := schemeYoneda S
  let := MorphismProperty.RespectsIso.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)
  apply MorphismProperty.relative_of_snd hf.rep
  intro T g
  let q := hf.rep.snd g
  let p := ha.rep.snd g
  let v := ha.rep.fst' g
  let hq : IsImmersion q.left := hf.property_snd g
  let hp : Etale p.left := ha.property_snd g
  let hps : Surjective p.left :=
    hs.projection g (ha.rep.fst g) p (ha.rep.isPullback g)
  let r := pullback.fst q p
  let j := pullback.snd q p
  let b := Y.map r ≫ hf.rep.fst g
  have houter : IsPullback b (Y.map j) f (Y.map v ≫ a) := by
    have h := ((IsPullback.of_hasPullback q p).map Y).paste_horiz (hf.rep.isPullback g)
    have hw : Y.map p ≫ g = Y.map v ≫ a := (ha.rep.isPullback' g).w.symm
    change IsPullback b (Y.map j) f (Y.map p ≫ g) at h
    rwa [hw] at h
  let l := hf.rep.lift b (j ≫ v) (by
    simpa only [Functor.map_comp, Category.assoc] using houter.w)
  have hl : IsPullback (Y.map l) (Y.map j) (Y.map (hf.rep.snd a)) (Y.map v) := by
    apply IsPullback.of_right _ _ (hf.rep.isPullback a)
    · simpa only [l, Y, Functor.relativelyRepresentable.lift_fst] using houter
    · change Y.map l ≫ Y.map (hf.rep.snd a) = Y.map j ≫ Y.map v
      rw [← Y.map_comp, ← Y.map_comp]
      exact Y.congr_map (hf.rep.lift_snd _ _ _)
  let hclosed : _root_.AlgebraicGeometry.IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback
      ((isPullback_of_map hl).map (Over.forget S)) hc
  exact @isClosedImmersion_of_etale_surjective_square _ _ _ _ _ _ _ _
    ((IsPullback.of_hasPullback q p).map (Over.forget S))
    hq.toIsPreimmersion hp hps hclosed

end Langlands.AlgebraicGeometry.AlgebraicSpace
