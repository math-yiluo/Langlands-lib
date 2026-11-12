import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Finiteness.Descent

/-! # Affine, finite and closed immersion properties under faithfully flat descent -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-- An affine source recovered by faithfully flat affine base change is identified
with the spectrum of its actual global sections. -/
def affineSourceIsoSpecOfAffinePullback
    {P X Y G : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ G}
    {π : X ⟶ Y} {q : G ⟶ Y} (h : IsPullback fst snd π q)
    [IsAffine Y] [IsAffine G] [Flat q] [Surjective q] [IsAffine P] : X ≅ Spec Γ(X, ⊤) :=
  have := FaithfullyFlatAffineDescent.isAffine_of_isPullback h
  X.isoSpec

set_option backward.isDefEq.respectTransparency false in
/-- Affine morphisms satisfy fpqc descent. -/
instance affine_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsAffineHom.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R A Y φ g hφ hg
  let : Surjective (Spec.map φ) := hφ.1
  let : Flat (Spec.map φ) := hφ.2
  let : IsAffineHom (pullback.fst (Spec.map φ) g) := hg
  have : IsAffine (Limits.pullback (Spec.map φ) g) :=
    isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
  have : IsAffine Y := FaithfullyFlatAffineDescent.isAffine_of_isPullback
    (IsPullback.of_hasPullback (Spec.map φ) g).flip
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Affine-and-ring properties satisfy fpqc descent once the ring property
codescends along faithfully flat ring maps. -/
theorem affineAnd_descendsAlong_fpqc (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    (Q : ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop)
    (hP : HasAffineProperty P (affineAnd Q)) (hQ : RingHom.RespectsIso Q)
    (hdesc : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat) :
    P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R A Y φ g hφ hg
  let : Surjective (Spec.map φ) := hφ.1
  let : Flat (Spec.map φ) := hφ.2
  have : IsAffine (Limits.pullback (Spec.map φ) g) :=
    (hP.iff_of_isAffine.mp hg).1
  have : IsAffine Y := FaithfullyFlatAffineDescent.isAffine_of_isPullback
    (IsPullback.of_hasPullback (Spec.map φ) g).flip
  wlog hY : ∃ B, Y = Spec B generalizing Y
  · rw [← P.cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.inv (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this (g := Y.isoSpec.inv ≫ g) ?_ inferInstance inferInstance ⟨_, rfl⟩
    rwa [heq, P.cancel_left_of_respectsIso]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong P (@Surjective.{u} ⊓ @Flat.{u})
    hdesc ?_ ?_ hφ hg
  · intro R A ψ hψ
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨Flat.SpecMap_iff.mp hψ.2, hψ.1.surj⟩
  · intro R A ψ
    exact HasAffineProperty.SpecMap_iff_of_affineAnd hP hQ ψ

/-- Closed immersions satisfy fpqc descent. -/
instance closedImmersion_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) :=
  affineAnd_descendsAlong_fpqc _ (fun f => Function.Surjective f) inferInstance
    RingHom.surjective_respectsIso RingHom.FaithfullyFlat.codescendsAlong_surjective

/-- Finite morphisms satisfy fpqc descent. -/
abbrev finite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsFinite.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) :=
  FpqcDescent.descendsAlong_isFinite_surjective_inf_flat_inf_quasicompact

set_option backward.isDefEq.respectTransparency false in
/-- Scheme properties satisfying fpqc descent and Zariski locality at the target
descend along surjective étale maps. -/
theorem descendsAlong_etale_surjective (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u})]
    [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u}) := by
  have : P.DescendsAlong
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) := by
    apply IsZariskiLocalAtTarget.descendsAlong
    rintro R X Y f g ⟨⟨hfS, hfF⟩, hfL⟩ H
    obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
      f.continuous (by simp) isOpen_univ isCompact_univ
    refine MorphismProperty.of_isPullback_of_descendsAlong
      (P := P) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g))
      ⟨⟨?_, inferInstance⟩,
        (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
    · exact ⟨fun x => have ⟨y, hyV, he⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, he⟩⟩
    · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H
  apply MorphismProperty.DescendsAlong.of_le
    (P := P) (Q := @Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})
  intro U V f hf
  let : Etale f := hf.1
  exact ⟨⟨hf.2, inferInstance⟩, inferInstance⟩

instance affine_descendsAlong_etale_surjective :
    MorphismProperty.DescendsAlong (@IsAffineHom.{u}) (@Etale.{u} ⊓ @Surjective.{u}) :=
  descendsAlong_etale_surjective _

instance closedImmersion_descendsAlong_etale_surjective :
    MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (@Etale.{u} ⊓ @Surjective.{u}) :=
  descendsAlong_etale_surjective _

instance finite_descendsAlong_etale_surjective :
    MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsFinite.{u})
      (@Etale.{u} ⊓ @Surjective.{u}) :=
  descendsAlong_etale_surjective _

instance openImmersion_descendsAlong_etale_surjective :
    MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (@Etale.{u} ⊓ @Surjective.{u}) :=
  descendsAlong_etale_surjective _

end Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
