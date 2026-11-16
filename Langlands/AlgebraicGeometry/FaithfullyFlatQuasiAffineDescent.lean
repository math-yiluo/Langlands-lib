import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Quasi-affineness descends along flat surjections of affine bases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent

/-- A scheme whose pullback along a flat surjection of affine bases is
quasi-affine is itself quasi-affine. -/
theorem isQuasiAffine_of_isPullback
    {P X Y B : Scheme.{u}} {p : P ⟶ X} {b : P ⟶ B}
    {f : X ⟶ Y} {q : B ⟶ Y} (h : IsPullback p b f q)
    [IsAffine Y] [IsAffine B] [Flat q] [Surjective q]
    [P.IsQuasiAffine] : X.IsQuasiAffine := by
  have : Surjective p :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have : QuasiCompact p :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip inferInstance
  have : CompactSpace X :=
    Function.Surjective.compactSpace p.continuous p.surjective
  have : QuasiSeparatedSpace X :=
    FieldExtensionAffineDescent.quasiSeparatedSpace_of_surjective p
  have hpo : IsPushout f.appTop q.appTop p.appTop b.appTop :=
    LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback h
  have hR := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hqflat : Flat (Spec.map q.appTop) :=
    Flat.SpecMap_iff.mpr (Scheme.Hom.flat_appTop q)
  have hqsurj : Surjective (Spec.map q.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine q)).mp
      inferInstance
  have hflat : Flat (Spec.map p.appTop) :=
    MorphismProperty.of_isPullback (P := @Flat) hR.flip hqflat
  have hsurj : Surjective (Spec.map p.appTop) :=
    MorphismProperty.of_isPullback (P := @Surjective) hR.flip hqsurj
  have hB : IsPullback B.toSpecΓ q (Spec.map q.appTop) Y.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality q).symm⟩
  have hbig := h.flip.paste_horiz hB
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality] at hbig
  have hpb : IsPullback P.toSpecΓ p (Spec.map p.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality p).symm hR.flip
  have : IsOpenImmersion X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ (inferInstanceAs (IsOpenImmersion P.toSpecΓ))
  constructor

/-- The canonical open in the affine hull obtained by quasi-affine descent. -/
noncomputable def affineHullOpen
    {P X Y B : Scheme.{u}} {p : P ⟶ X} {b : P ⟶ B}
    {f : X ⟶ Y} {q : B ⟶ Y} (h : IsPullback p b f q)
    [IsAffine Y] [IsAffine B] [Flat q] [Surjective q]
    [P.IsQuasiAffine] : (Spec Γ(X, ⊤)).Opens := by
  letI := isQuasiAffine_of_isPullback h
  exact X.toSpecΓ.opensRange

/-- The descended scheme identified with its canonical open in the affine hull. -/
noncomputable def affineHullOpenIso
    {P X Y B : Scheme.{u}} {p : P ⟶ X} {b : P ⟶ B}
    {f : X ⟶ Y} {q : B ⟶ Y} (h : IsPullback p b f q)
    [IsAffine Y] [IsAffine B] [Flat q] [Surjective q]
    [P.IsQuasiAffine] : X ≅ (affineHullOpen h).toScheme := by
  letI := isQuasiAffine_of_isPullback h
  exact X.toSpecΓ.isoOpensRange

@[reassoc (attr := simp)]
theorem affineHullOpenIso_hom_ι
    {P X Y B : Scheme.{u}} {p : P ⟶ X} {b : P ⟶ B}
    {f : X ⟶ Y} {q : B ⟶ Y} (h : IsPullback p b f q)
    [IsAffine Y] [IsAffine B] [Flat q] [Surjective q]
    [P.IsQuasiAffine] :
    (affineHullOpenIso h).hom ≫ (affineHullOpen h).ι = X.toSpecΓ := by
  have := isQuasiAffine_of_isPullback h
  exact X.toSpecΓ.isoOpensRange_hom_ι

end Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent
