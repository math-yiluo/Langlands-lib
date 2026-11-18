import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleStatement
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAffinePullbackTests
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability

/-! # Conditional reflection of étaleness for affine test points -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The pullback-existence statement also controls any supplied pullback square,
by its categorical uniqueness. -/
theorem etale_snd_of_isPullback_of_etalePullbacks
    (hPullback : LocalizedEtalePullbackStatement.{u, u} K)
    {T A B Y : LocalizedCategory.{u, u, u} (K := K)}
    {p : T ⟶ A} {q : T ⟶ B} {a : A ⟶ Y} {b : B ⟶ Y}
    (h : IsPullback p q a b) (ha : etale a) : etale q := by
  obtain ⟨T', p', q', h', hq'⟩ := hPullback a b ha
  rw [← h.isoIsPullback_hom_snd _ _ h']
  exact etale_comp (etale_of_isIso _) hq'

/-- The étale clause of the affine comparison reflects localized étaleness
when its passage to finite pieces on the original atlas is supplied. -/
theorem ringHom_etale_of_localizedHom_etale
    (hAffine : AffineAnalytification.AffineAnalytificationEtaleStatement.{u, u, u})
    (hRecognition : ∀ (A B : Type u) [CommRing A] [Algebra K A]
      [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B), etale (AffineAnalytification.localizedHom K P Q f) →
      AffinoidAtlasPresentation.StrongHom.IsEtale
        (A := AffineAnalytification.presentation K Q)
        (B := AffineAnalytification.presentation K P)
        (AffineAnalytification.saturatedHom K P Q f))
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (hf : etale (AffineAnalytification.localizedHom K P Q f)) :
    f.toRingHom.Etale := by
  exact (hAffine K A B P Q f).2.2.mpr (hRecognition A B P Q f hf)

set_option backward.isDefEq.respectTransparency false in
/-- An affine test point is étale if its analytified map is étale, assuming
localized étale pullbacks and reflection for actual affine algebra maps. -/
theorem isEtale_pointHom_of_etale_of_affineReflection
    (hPullback : LocalizedEtalePullbackStatement.{u, u} K)
    (hAffineReflect : ∀ (A B : Type u) [CommRing A] [Algebra K A]
      [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B), etale (AffineAnalytification.localizedHom K P Q f) →
        f.toRingHom.Etale)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hXsep : IsSeparated X) (hXLFT : LocallyOfFiniteTypeOverBase X)
    {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p)
    {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X A)
    (hx : etale (p A P x)) : AlgebraicSpace.IsEtale (pointHom K x) := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let a := pointHom K x
  apply isEtale_of_affine_target_tests a
  intro V _ b hb
  let : LocallyOfFiniteType V.hom := locallyOfFiniteType_of_isEtale hXLFT b hb
  let T := pairPullback a b
  let : IsAffine T.left := isAffine_pairPullback a b hXsep
  let : LocallyOfFiniteType T.hom := locallyOfFiniteType_pairPullback a b hb
  let B := AffineCoordinateRing K V
  let C := AffineCoordinateRing K T
  let Q := FinitePolynomialPresentation.ofFiniteType K B
  let R := FinitePolynomialPresentation.ofFiniteType K C
  let eV := affineSchemeOverIso K V
  let eT := affineSchemeOverIso K T
  let f : A →ₐ[K] C := affineRingPointEquiv K A C (eT.inv ≫ pairPullbackFst a b)
  let g : B →ₐ[K] C := affineRingPointEquiv K B C
    ((eT.inv ≫ pairPullbackSnd a b) ≫ eV.hom)
  have hf : ringTestMap K f = eT.inv ≫ pairPullbackFst a b :=
    ringTestMap_affineRingPointEquiv K _
  have hg : ringTestMap K g = (eT.inv ≫ pairPullbackSnd a b) ≫ eV.hom :=
    ringTestMap_affineRingPointEquiv K _
  let y : RingPoints K X B := uliftYonedaEquiv ((schemeYoneda _).map eV.inv ≫ b)
  have hSquare : IsPullback ((schemeYoneda _).map (ringTestMap K f))
      ((schemeYoneda _).map (ringTestMap K g)) (pointHom K x) (pointHom K y) := by
    apply (pairPullback_isPullback a b).of_iso'
      ((schemeYoneda _).mapIso eT.symm) (Iso.refl _)
      ((schemeYoneda _).mapIso eV.symm) (Iso.refl _)
    · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
        hf, Functor.map_comp]
    · simp only [Functor.mapIso_hom, Iso.symm_hom, hg,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, a]
    · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
        pointHom, y, Equiv.symm_apply_apply]
  have hAnalytic := hp.isPullback P Q R f g x y hSquare
  have hEtaleG : etale (AffineAnalytification.localizedHom K Q R g) :=
    etale_snd_of_isPullback_of_etalePullbacks K hPullback hAnalytic hx
  have hRing := hAffineReflect B C Q R g hEtaleG
  let : Etale (ringTestMap K g).left :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)
      (φ := CommRingCat.ofHom g.toRingHom)).mpr hRing
  have he : (eT.hom ≫ ringTestMap K g) ≫ eV.inv = pairPullbackSnd a b := by
    rw [hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← he]
  change Etale ((eT.hom.left ≫ (ringTestMap K g).left) ≫ eV.inv.left)
  infer_instance

/-- Source descent, localized étale pullbacks and reflection for actual affine
algebra maps imply the complete unchanged algebraic-space comparison. -/
theorem spaceAnalytificationEtaleStatement_of_sourceDescent_of_affineReflection
    (hSource : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type (u + 1)) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F)
    (hPullback : ∀ (K : Type u) [NontriviallyNormedField K]
      [IsUltrametricDist K] [CompleteSpace K], LocalizedEtalePullbackStatement.{u, u} K)
    (hAffineReflect : ∀ (K : Type u) [NontriviallyNormedField K]
      [IsUltrametricDist K] [CompleteSpace K]
      (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B), etale (AffineAnalytification.localizedHom K P Q f) →
        f.toRingHom.Etale) : SpaceAnalytificationEtaleStatement.{u} := by
  intro K _ _ _ X' X f _ hX'LFT hXsep hXLFT Y' Y p' p hp' hp F hF
  apply isEtaleMorphism_iff_etale_of_sourceDescent_of_pointReflection K hSource f hX'LFT
    hp' hp _ F hF
  intro A _ _ P x hx
  exact isEtale_pointHom_of_etale_of_affineReflection K (hPullback K) (hAffineReflect K)
    hXsep hXLFT hp P x hx

/-- The affine comparison can supply the affine reflection premise after
recognition on the original affine atlas has been proved. All four inputs
remain hypotheses of this conditional theorem. -/
theorem spaceAnalytificationEtaleStatement_of_inputs
    (hSource : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type (u + 1)) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F)
    (hPullback : ∀ (K : Type u) [NontriviallyNormedField K]
      [IsUltrametricDist K] [CompleteSpace K], LocalizedEtalePullbackStatement.{u, u} K)
    (hAffine : AffineAnalytification.AffineAnalytificationEtaleStatement.{u, u, u})
    (hRecognition : ∀ (K : Type u) [NontriviallyNormedField K]
      [IsUltrametricDist K] [CompleteSpace K]
      (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B), etale (AffineAnalytification.localizedHom K P Q f) →
      AffinoidAtlasPresentation.StrongHom.IsEtale
        (A := AffineAnalytification.presentation K Q)
        (B := AffineAnalytification.presentation K P)
        (AffineAnalytification.saturatedHom K P Q f)) :
    SpaceAnalytificationEtaleStatement.{u} := by
  apply spaceAnalytificationEtaleStatement_of_sourceDescent_of_affineReflection hSource
    hPullback
  intro K _ _ _ A B _ _ _ _ P Q f hf
  exact ringHom_etale_of_localizedHom_etale K hAffine (hRecognition K) P Q f hf

end Langlands.Analytic.SpaceAnalytification
