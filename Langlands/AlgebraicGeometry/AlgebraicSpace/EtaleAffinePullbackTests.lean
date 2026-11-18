import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAffineTests
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasProperty
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Detecting étale scheme points by affine étale target charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

set_option backward.isDefEq.respectTransparency false in
/-- A scheme point is étale if its actual pullback projection to every affine
étale chart of the target is étale. -/
theorem isEtale_of_affine_target_tests {U : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (hTests : ∀ (V : Over (Spec (CommRingCat.of K))) [IsAffine V.left]
      (b : (schemeYoneda _).obj V ⟶ X.presheaf), IsEtale b →
      Etale (pairPullbackSnd a b).left) : IsEtale a := by
  let : MorphismProperty.DescendsAlong (@Etale.{u}) (@Etale.{u} ⊓ @Surjective.{u}) :=
    SchemeFlatPropertyDescent.descendsAlong_etale_surjective _
  obtain ⟨T, b, _, hb, hs⟩ := X.exists_atlas
  let hr := X.representable_from_scheme a
  apply relativeProperty_of_etale_atlas (@Etale.{u}) hr b hb hs
  let q := hr.snd b
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u})
    (SchemeOpenChart.pullbackOpenCover T.left.affineCover q)
  intro i
  change T.left.affineCover.I₀ at i
  let V := SchemeOpenChart.obj T.left.affineCover i
  let j : V ⟶ T := SchemeOpenChart.map T.left.affineCover i
  let c := (schemeYoneda _).map j ≫ b
  have hj : Etale j.left := inferInstance
  have hc : IsEtale c := (isEtale_map j hj).comp hb
  let : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have ht : Etale (pairPullbackSnd a c).left := hTests V c hc
  have hOuter : IsPullback
      ((schemeYoneda _).map (pullback.fst q j) ≫ hr.fst b)
      ((schemeYoneda _).map (pullback.snd q j)) a c :=
    ((IsPullback.of_hasPullback q j).map (schemeYoneda _)).paste_horiz (hr.isPullback b)
  let e := (schemeYoneda _).preimageIso
    (hOuter.isoIsPullback _ _ (pairPullback_isPullback a c))
  have he : e.hom ≫ pairPullbackSnd a c = pullback.snd q j := by
    apply (schemeYoneda _).map_injective
    rw [Functor.map_comp]
    change (schemeYoneda _).map ((schemeYoneda _).preimage _) ≫ _ = _
    rw [Functor.map_preimage]
    exact hOuter.isoIsPullback_hom_snd _ _ (pairPullback_isPullback a c)
  have hSnd : Etale (pullback.snd q j).left := by
    rw [← he]
    change Etale (e.hom.left ≫ (pairPullbackSnd a c).left)
    infer_instance
  change Etale ((pullback.fst q j).left ≫ q.left)
  have hw : (pullback.fst q j).left ≫ q.left =
      (pullback.snd q j).left ≫ j.left :=
    congrArg (fun z => z.left) (pullback.condition (f := q) (g := j))
  rw [hw]
  infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
