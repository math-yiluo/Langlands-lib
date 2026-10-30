import Langlands.AbelianScheme.FieldFiniteSurjectiveEndomorphismFlatStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FiniteGenericFlatProof
import Langlands.GroupScheme.TranslationFlatProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Flatness of finite surjective abelian endomorphisms over fields -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme

private lemma flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact Module.Flat.of_flat_tensorProduct R T S

private instance flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat flat_codescendsAlong_faithfullyFlat

private lemma pullback_over_map_isPullback
    {S S' : Scheme.{u}} (b : S' ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback b).map f).left
      (pullback.fst X.hom b) (pullback.fst Y.hom b) f.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom b) (h₂₂ := Y.hom) (v₁₃ := b)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback X.hom b).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback Y.hom b).flip

set_option backward.isDefEq.respectTransparency false in
theorem fieldFiniteSurjectiveEndomorphismFlat :
    FieldFiniteSurjectiveEndomorphismFlatStatement.{u} := by
  intro K _ G _ f hs _ hc hf hsurj
  let : Smooth G.X.hom := hs
  let : GeometricallyConnected G.X.hom := hc
  let : IsFinite f.hom.hom.left := hf
  let : Surjective f.hom.hom.left := hsurj
  let Ω : Type u := AlgebraicClosure K
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let GΩ := (Over.pullback b).mapGrp.obj G
  let fΩ : GΩ ⟶ GΩ := (Over.pullback b).mapGrp.map f
  have hsq : IsPullback fΩ.hom.hom.left (pullback.fst G.X.hom b)
      (pullback.fst G.X.hom b) f.hom.hom.left :=
    pullback_over_map_isPullback b f.hom.hom
  have hfiniteΩ : IsFinite fΩ.hom.hom.left :=
    MorphismProperty.of_isPullback hsq.flip hf
  have hsurjΩ : Surjective fΩ.hom.hom.left :=
    MorphismProperty.of_isPullback hsq.flip hsurj
  have hsΩ : Smooth GΩ.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : Smooth GΩ.X.hom := hsΩ
  have hnoethΩ : IsLocallyNoetherian GΩ.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian GΩ.X.hom
  have hintegralΩ : IsIntegral GΩ.X.left := by
    let : GeometricallyIntegral G.X.hom :=
      Langlands.AbelianScheme.smoothGeometricIntegrality K G.X.left G.X.hom hs hc
    change IsIntegral (pullback G.X.hom b)
    exact GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd G.X.hom b)
  have hopenΩ := Langlands.AlgebraicGeometry.finiteGenericFlat
    GΩ.X.left GΩ.X.left fΩ.hom.hom.left
    hintegralΩ hnoethΩ hfiniteΩ
  have hflatΩ : Flat fΩ.hom.hom.left :=
    translationFlat Ω GΩ fΩ inferInstance hfiniteΩ hsurjΩ hopenΩ
  have hb : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) b := by
    dsimp [b]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let : Surjective b := hb.1.1
  let : Flat b := hb.1.2
  let : QuasiCompact b := hb.2
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ?_ hflatΩ
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end Langlands.GroupScheme
