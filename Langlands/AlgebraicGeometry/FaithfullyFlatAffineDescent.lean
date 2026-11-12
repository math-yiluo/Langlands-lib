import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof

/-! # Affineness descends along flat surjective morphisms of affine schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent

/-- If the base change of `π : X ⟶ Y` along a flat surjective morphism `q : G ⟶ Y` of affine
schemes is affine, then `X` is affine. -/
theorem isAffine_of_isPullback {P X Y G : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ G}
    {π : X ⟶ Y} {q : G ⟶ Y} (h : IsPullback fst snd π q) [IsAffine Y] [IsAffine G]
    [Flat q] [Surjective q] [IsAffine P] : IsAffine X := by
  have : Surjective fst :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have : QuasiCompact fst :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip inferInstance
  have : CompactSpace X := Function.Surjective.compactSpace fst.continuous fst.surjective
  have : QuasiSeparatedSpace X :=
    FieldExtensionAffineDescent.quasiSeparatedSpace_of_surjective fst
  have hpo : IsPushout π.appTop q.appTop fst.appTop snd.appTop :=
    LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback h
  have hR := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hqflat : Flat (Spec.map q.appTop) := Flat.SpecMap_iff.mpr (Scheme.Hom.flat_appTop q)
  have hqsurj : Surjective (Spec.map q.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine q)).mp
      inferInstance
  have hflat : Flat (Spec.map fst.appTop) :=
    MorphismProperty.of_isPullback (P := @Flat) hR.flip hqflat
  have hsurj : Surjective (Spec.map fst.appTop) :=
    MorphismProperty.of_isPullback (P := @Surjective) hR.flip hqsurj
  have hG : IsPullback G.toSpecΓ q (Spec.map q.appTop) Y.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality q).symm⟩
  have hbig := h.flip.paste_horiz hG
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality] at hbig
  have hpb : IsPullback P.toSpecΓ fst (Spec.map fst.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality fst).symm hR.flip
  have hiso : IsIso X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ (inferInstanceAs (IsIso P.toSpecΓ))
  exact ⟨hiso⟩

end Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent
