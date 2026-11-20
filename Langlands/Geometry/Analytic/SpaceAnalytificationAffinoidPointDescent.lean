import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing
import Langlands.Geometry.Analytic.EtaleCoverHomExt
import Langlands.Geometry.Analytic.FiniteAffinoidLocalizedHomDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidPointComparison

/-! # Descent of affinoid-algebra points in analytifications -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTestMap)
open PresentedAffinoidAlgebra.AffinoidPushout SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

private theorem ringTestMap_isPullback_of_finite (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) :
    IsPullback (ringTestMap K (leftMap f f).toAlgHom) (ringTestMap K (rightMap f f).toAlgHom)
      (ringTestMap K f.toAlgHom) (ringTestMap K f.toAlgHom) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let e := RingEquiv.ofBijective (tensorComparison f f) (finiteTensorComparison A B B f f hf)
  have hpo := (CommRingCat.isPushout_tensorProduct A B B).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
    (f' := CommRingCat.ofHom f.toAlgHom.toRingHom)
    (g' := CommRingCat.ofHom f.toAlgHom.toRingHom)
    (inl' := CommRingCat.ofHom (leftMap f f).toAlgHom.toRingHom)
    (inr' := CommRingCat.ofHom (rightMap f f).toAlgHom.toRingHom)
    rfl rfl
    (CommRingCat.hom_ext (RingHom.ext fun b => tensorComparison_tensorRight f f b))
    (CommRingCat.hom_ext (RingHom.ext fun b => tensorComparison_tensorLeft f f b))
  let U := Over.forget (Spec (CommRingCat.of K))
  have hsp : IsPullback (U.map (ringTestMap K (leftMap f f).toAlgHom))
      (U.map (ringTestMap K (rightMap f f).toAlgHom))
      (U.map (ringTestMap K f.toAlgHom)) (U.map (ringTestMap K f.toAlgHom)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  exact hsp.of_map_of_faithful U

/-- Analytic matching over the actual affinoid self-pullback gives a descended
ring-valued point. -/
theorem affinoidPointHom_descend_matching
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (b : RingPoints K X B)
    (hmatch : localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} (leftMap f f)) ≫
        affinoidPointHom hp hX hft B b =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} (rightMap f f)) ≫
        affinoidPointHom hp hX hft B b) :
    ∃ a : RingPoints K X A, RingPoints.changeRing f.toAlgHom a = b := by
  have hff := SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective
    f ((f.algebraicallyFiniteEtale_iff).mp he).2.1 hsurj
  have hspec := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f.toAlgHom.toRingHom)).2 hff
  let : Flat (ringTestMap K f.toAlgHom).left := hspec.1
  let : Surjective (ringTestMap K f.toAlgHom).left := hspec.2
  let : LocallyOfFinitePresentation (ringTestMap K f.toAlgHom).left :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      ((f.algebraicallyFiniteEtale_iff).mp he).2.2.2
  apply ProductPointsDescent.exists_pullback_eq X (ringTestMap K f.toAlgHom)
    (ringTestMap_isPullback_of_finite f hf) b
  change RingPoints.changeRing (leftMap f f).toAlgHom b =
    RingPoints.changeRing (rightMap f f).toAlgHom b
  apply affinoidPointHom_injective hp hX hft (algebra f f)
  rw [affinoidPointHom_changeRing, affinoidPointHom_changeRing]
  exact hmatch

private theorem localized_map_surjective (f : BoundedAlgHom K A B)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    Function.Surjective
      (localizedSpaceFunctor.map (localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f))) := by
  intro x
  obtain ⟨a, rfl⟩ := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} A).surjective x
  obtain ⟨b, hb⟩ := hsurj a
  exact ⟨SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} B b,
    (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} f b).trans
      (congrArg (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} A) hb)⟩

/-- A localized affinoid map is in the image of the ring-point comparison
if its restriction to a finite étale surjective affinoid cover is in the image. -/
def AffinoidPointHomFiniteEtaleDescentStatement
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) :
    Prop :=
  ∀ {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B),
    f.IsFiniteBanach → f.AlgebraicallyFiniteEtale →
    Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom) →
    ∀ (m : localizedAffinoidSpectrum A ⟶ Y) (b : RingPoints K X B),
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f) ≫ m =
        affinoidPointHom hp hX hft B b →
      ∃ a : RingPoints K X A, affinoidPointHom hp hX hft A a = m

theorem affinoidPointHom_descend
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X) :
    AffinoidPointHomFiniteEtaleDescentStatement hp hX hft := by
  intro A B f hf he hsurj m b hm
  have hpb := SmallAffinoidSpectrum.pushout_localized_isPullback.{u, u} f f
  have hmatch : localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} (leftMap f f)) ≫
        affinoidPointHom hp hX hft B b =
      localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} (rightMap f f)) ≫
        affinoidPointHom hp hX hft B b := by
    rw [← hm, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ m) hpb.w
  obtain ⟨a, ha⟩ := affinoidPointHom_descend_matching hp hX hft f hf he hsurj b hmatch
  let F : localizedAffinoidSpectrum B ⟶ localizedAffinoidSpectrum A :=
    localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} f)
  refine ⟨a, etaleCoverHomExt (fun _ : Unit => F) (fun _ => ?_) (fun x => ?_) _ _ (fun _ => ?_)⟩
  · exact SmallAffinoidSpectrum.map_etale_of_finite_pointwiseEtale f
      finiteBanachPushout finiteTensorComparison hf he.isEtaleAtPoint
  · exact ⟨(), localized_map_surjective f hsurj x⟩
  · rw [← affinoidPointHom_changeRing hp hX hft f, ha, hm]

end Langlands.Analytic.SpaceAnalytification
