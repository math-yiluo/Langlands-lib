import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.Torus.WeylPointTransport

/-! # Smooth closed normalizers of relative tori over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open Corepresented CharacterAction

/-- A locally finitely presented closed representative of a split-torus normalizer
is smooth over any affine base. -/
theorem splitTorusNormalizer_smooth_overRing
    {R : CommRingCat.{u}} {G N : GroupScheme (Spec R)}
    {T : CommGroupScheme (Spec R)} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hnfp : LocallyOfFinitePresentation n.hom.hom.left)
    (hnrep : (torusNormalizer t).IsRepresentedBy n) : Smooth N.X.hom := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion t.hom.hom.left := ht
  let : IsClosedImmersion n.hom.hom.left := hn
  let : LocallyOfFinitePresentation n.hom.hom.left := hnfp
  let : Algebra.Smooth R (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  let e := AffineCoordinates.corepresentation G
  obtain ⟨I, hI⟩ := exists_ideal_range (AffineCoordinates.coordinateHom t)
  obtain ⟨J, hJ⟩ := exists_ideal_range (AffineCoordinates.coordinateHom n)
  let hcut := isCutOutBy_range hJ
  have hncoord := hnrep.comp_iso (AffineCoordinates.groupSchemeIso G).symm
  have hnormalizer :
      (SubgroupFunctor.range (AffineCoordinates.coordinateHom t)).normalizer =
        (torusNormalizer t).comap (AffineCoordinates.groupSchemeIso G).hom := by
    simpa only [AffineCoordinates.coordinateHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, torusNormalizer] using
      SubgroupFunctor.normalizer_range_eq_comap_of_iso
        (AffineCoordinates.coordinateHom t) (AffineCoordinates.groupSchemeIso G)
  have hrangeN : SubgroupFunctor.range (AffineCoordinates.coordinateHom n) =
      (SubgroupFunctor.range (AffineCoordinates.coordinateHom t)).normalizer :=
    hncoord.2.trans hnormalizer.symm
  obtain ⟨K, _, ⟨eT⟩⟩ := hT
  let : Fintype K := Fintype.ofFinite K
  let dT : (Diagonalizable.groupScheme R (K → ℤ)).toGrp ≅ T.toGrp :=
    Diagonalizable.splitIso R (AddEquiv.refl (K → ℤ)) ≪≫ eT.symm
  let jD := dT.hom ≫ AffineCoordinates.coordinateHom t
  let : Mono jD.hom.hom := by
    let : IsClosedImmersion jD.hom.hom.left :=
      IsClosedSubgroup.iso_comp dT (i := AffineCoordinates.coordinateHom t)
        (inferInstance : IsClosedImmersion (AffineCoordinates.coordinateHom t).hom.hom.left)
    have : Mono jD.hom.hom.left :=
      SurjectiveOnStalks.mono_of_injective jD.hom.hom.left.isClosedEmbedding.injective
    exact Over.mono_of_mono_left _
  let emb := diagonalizableEmbedding e jD
  have hrange : ∀ A, emb.range A =
      affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom t)) A := by
    intro A
    rw [diagonalizableEmbedding_range, SubgroupFunctor.range_iso_comp]
  have hlift : HasSquareZeroLifting
      (affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom n))) := by
    rw [hrangeN]
    have h := hasSquareZeroLifting_normalizerFamily e emb
    have hfam : normalizerFamily emb.range =
        affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom t)).normalizer := by
      funext A
      rw [affineSubgroups_normalizer hI, funext hrange]
    rwa [hfam] at h
  let : Algebra.FormallySmooth R (AffineCoordinates.algebra G ⧸ J) :=
    formallySmooth_of_hasSquareZeroLifting hcut hlift
  have hcutrep : (SubgroupFunctor.range (AffineCoordinates.coordinateHom n)).IsRepresentedBy
      (cutHom hcut) := by
    apply isRepresentedBy_cutHom_affineSubgroups
    exact isAffineCutOutBy_of_isCutOutBy hcut
  let eN : N ≅ cutGroupScheme hcut :=
    hncoord.isoOfIsRepresentedBy (by rw [← hncoord.2]; exact hcutrep)
  have hNs : LocallyOfFinitePresentation N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have hcutfp : LocallyOfFinitePresentation (cutGroupScheme hcut).X.hom := by
    have : IsIso eN.inv.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eN.symm)).hom)
    rw [← Over.w eN.inv.hom.hom]
    infer_instance
  have hfp : Algebra.FinitePresentation R (AffineCoordinates.algebra G ⧸ J) := by
    exact RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp hcutfp)
  let : Algebra.Smooth R (AffineCoordinates.algebra G ⧸ J) :=
    { finitePresentation := hfp
      formallySmooth := inferInstance }
  exact smooth_of_over_iso ((Grp.forget _).mapIso eN) (smooth_cutGroupScheme hcut)

/-- Every representative of a closed split-torus normalizer in a smooth
relatively affine group is smooth over an arbitrary base. -/
theorem splitTorusNormalizer_smooth {S : Scheme.{u}}
    {G N : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n) :
    Smooth N.X.hom := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    S.affineOpenCover.openCover.changeProp (fun k => inferInstance)
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  obtain ⟨L, j, hj, hjfp, hjrep⟩ :=
    RelativeTorus.closedNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t) (RelativeTorus.IsTorus.of_isSplitTorus (hT.baseChange b))
      (ht.baseChange b)
  have hLs : Smooth L.X.hom :=
    splitTorusNormalizer_smooth_overRing
      (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t) (hT.baseChange b) (ht.baseChange b) j hj hjfp hjrep
  have hnbase : (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map n) := by
    rw [torusNormalizer_baseChange]
    exact hnrep.baseChange b
  exact smooth_of_over_iso ((Grp.forget _).mapIso
    (hnbase.isoOfIsRepresentedBy hjrep)) hLs

/-- Every representative of the normalizer of a closed relative torus is
smooth over an arbitrary base. -/
theorem relativeTorusNormalizer_smooth {S : Scheme.{u}}
    {G N : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n) :
    Smooth N.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hnbase : (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map n) := by
    rw [torusNormalizer_baseChange]
    exact hnrep.baseChange b
  exact splitTorusNormalizer_smooth (T := (CommGroupScheme.baseChange b).obj T)
    (B.map t) (h𝒰 k) (ht.baseChange b) (B.map n) hnbase

/-- A chosen smooth closed representative of the actual relative-torus
normalizer, with locally finitely presented inclusion. -/
def relativeTorusSmoothNormalizerModel {S : Scheme.{u}}
    {G : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) :
    Σ N : GroupScheme S, {n : N ⟶ G // IsClosedSubgroup n ∧
      LocallyOfFinitePresentation n.hom.hom.left ∧ Smooth N.X.hom ∧
      (torusNormalizer t).IsRepresentedBy n} := by
  let N := RelativeTorus.normalizerGroupScheme t hT ht
  let n : N ⟶ G := RelativeTorus.normalizerHom t hT ht
  have hn := RelativeTorus.normalizerHom_spec t hT ht
  exact ⟨N, n, hn.1, hn.2.1,
    relativeTorusNormalizer_smooth t hT ht n hn.2.2, hn.2.2⟩

end Langlands.GroupScheme
