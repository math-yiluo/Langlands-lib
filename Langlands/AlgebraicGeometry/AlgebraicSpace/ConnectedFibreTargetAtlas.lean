import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreFieldTests
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointTopologyIso
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Connected fibres tested on a surjective étale target atlas -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Over an algebraically closed field, a surjective étale chart lifts every section. -/
theorem exists_lift_atlas_algClosed {F : Presheaf S} {V : Over S}
    (b : (schemeYoneda S).obj V ⟶ F) (hb : IsEtale b) (hs : IsSurjective b)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : (schemeYoneda S).obj (Over.mk s) ⟶ F) :
    ∃ t : Over.mk s ⟶ V, (schemeYoneda S).map t ≫ b = y := by
  let hr := hb.representable
  let p := hr.snd y
  have hpe : Etale p.left := hb.projection y (hr.fst y) p (hr.isPullback y)
  have hps : Surjective p.left := hs.projection y (hr.fst y) p (hr.isPullback y)
  let := hpe
  obtain ⟨z, _⟩ := hps.surj (IsLocalRing.closedPoint K)
  obtain ⟨x, hx, _⟩ := FieldSchemePoints.exists_closed_specialization p.left z
  let u : Spec (CommRingCat.of K) ⟶ (hr.pullback y).left := pointOfClosedPoint p.left x hx
  have hu : u ≫ p.left = 𝟙 _ := pointOfClosedPoint_comp p.left x hx
  let uS : Over.mk s ⟶ hr.pullback y := Over.homMk u (by
    rw [← Over.w p, ← Category.assoc, hu]
    exact Category.id_comp s)
  have hup : uS ≫ p = 𝟙 (Over.mk s) := Over.OverMorphism.ext hu
  refine ⟨uS ≫ hr.fst' y, ?_⟩
  rw [Functor.map_comp, Category.assoc, (hr.isPullback' y).w,
    ← Category.assoc, ← Functor.map_comp, hup, (schemeYoneda S).map_id (Over.mk s),
    Category.id_comp]

/-- A cartesian square identifies a second fibre with the direct fibre. -/
def iteratedFibrePullbackIso {W X A Y : Presheaf S}
    {a : W ⟶ X} {p : W ⟶ A} {f : X ⟶ Y} {b : A ⟶ Y}
    (h : IsPullback a p f b) {H : Presheaf S} (y : H ⟶ A) :
    Limits.pullback p y ≅ Limits.pullback f (y ≫ b) :=
  ((IsPullback.of_hasPullback p y).paste_horiz h).isoPullback

/-- The target-atlas pullback tests nonempty geometrically connected fibres. -/
theorem hasGeometricallyConnectedFibres_iff_targetAtlas {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
    (hb : IsEtale b) (hs : IsSurjective b) :
    HasGeometricallyConnectedFibres f ↔
      HasGeometricallyConnectedFibres
        (FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y)) := by
  let b₀ : (schemeToSpace S).obj V ⟶ Y := homMk b
  let h := FibreProduct.isPullback_presheaf f b₀
  constructor
  · intro hf K _ s y
    let e := iteratedFibrePullbackIso h y
    let := pointTopology (Limits.pullback (hom (FibreProduct.snd f b₀)) y)
    let := pointTopology (Limits.pullback (hom f) (y ≫ hom b₀))
    exact (Points.isoHomeomorph e).connectedSpace_iff.mpr (hf K s (y ≫ b))
  · intro hf
    apply (hasGeometricallyConnectedFibres_iff_algClosed f).mpr
    intro K _ _ s y
    obtain ⟨t, ht⟩ := exists_lift_atlas_algClosed b hb hs K s y
    let e : Limits.pullback (hom (FibreProduct.snd f b₀)) ((schemeYoneda S).map t) ≅
        Limits.pullback (hom f) y :=
      iteratedFibrePullbackIso h ((schemeYoneda S).map t) ≪≫
        Limits.pullback.congrHom rfl (show (schemeYoneda S).map t ≫ hom b₀ = y from ht)
    let := pointTopology
      (Limits.pullback (hom (FibreProduct.snd f b₀)) ((schemeYoneda S).map t))
    let := pointTopology (Limits.pullback (hom f) y)
    exact (Points.isoHomeomorph e).connectedSpace_iff.mp
      (hf K s ((schemeYoneda S).map t))

end Langlands.AlgebraicGeometry.AlgebraicSpace
