import Langlands.Algebra.ProjectiveTensorFiniteEquations
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizer
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.RelativeNormalizerSmooth
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.FiniteStability

/-! # Smooth normalizers of subgroups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace Diagonalizable

/-- A group algebra of a finitely generated abelian group is finitely
presented over any commutative coefficient ring. -/
theorem finitePresentation_groupAlgebra_of_fg
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    Algebra.FinitePresentation R (AddMonoidAlgebra R M) := by
  let : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ M) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FinitePresentation.equiv (AddMonoidAlgebra.scalarTensorEquiv ℤ R (M := M))

end Diagonalizable

namespace Corepresented

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Ideal B} [Module.Projective R (B ⧸ I)]

/-- A finitely generated subgroup ideal gives finitely many equations for
the full normalizer, without a noetherian hypothesis. -/
theorem subgroupNormalizerIdeal_fg (hI : I.FG) : (subgroupNormalizerIdeal e I).FG := by
  exact Submodule.FG.sup
    (coefficientIdeal_image_ideal_fg (e.homEquiv.symm (universalConjugate e I)).hom hI)
    (coefficientIdeal_image_ideal_fg (e.homEquiv.symm (universalInvConjugate e I)).hom hI)

/-- A finite-type ambient coordinate algebra gives finitely many equations
for the centralizer against projective subgroup coordinates. -/
theorem subgroupCentralizerIdeal_fg [Algebra.FiniteType R B] :
    (subgroupCentralizerIdeal e I).FG :=
  coefficientIdeal_difference_fg
    (e.homEquiv.symm (universalLeftPoint e I * universalCutPoint e I B)).hom
    (e.homEquiv.symm (universalCutPoint e I B * universalLeftPoint e I)).hom

end Corepresented

open Corepresented CharacterAction

/-- The actual normalizer of a closed finite-character diagonalizable
subgroup is smooth over an arbitrary coefficient ring. -/
theorem diagonalizableNormalizer_smooth_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G N : GroupScheme (Spec R)} [IsAffine G.X.left] [Smooth G.X.hom]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hj : IsClosedSubgroup j)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range j).normalizer.IsRepresentedBy n) :
    Smooth N.X.hom := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Algebra.Smooth R (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  let e := AffineCoordinates.corepresentation G
  let j' := AffineCoordinates.coordinateHom j
  let : IsClosedImmersion j'.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (AffineCoordinates.coordinateHom j).hom.hom.left)
  let : Mono j'.hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective j'.hom.hom.left.isClosedEmbedding.injective
  let : Mono j'.hom.hom := Over.mono_of_mono_left _
  obtain ⟨I, hI⟩ := exists_ideal_range j'
  let hcut := isCutOutBy_range hI
  have hrep₁ : (SubgroupFunctor.range j').IsRepresentedBy j' :=
    ⟨inferInstance, rfl⟩
  have hrep₂ : (SubgroupFunctor.range j').IsRepresentedBy (cutHom hcut) :=
    isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_range hI)
  let eH : (Diagonalizable.groupScheme R M).toGrp ≅ cutGroupScheme hcut :=
    hrep₁.isoOfIsRepresentedBy hrep₂
  let eA : CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I) ≅
      ((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop :=
    (affineSectionsIso (CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I))).symm ≪≫
      ((algΓ R).mapIso ((Grp.forget _).mapIso eH)).unop
  let eQ : (AffineCoordinates.algebra G ⧸ I) ≃ₐ[R] AddMonoidAlgebra R M :=
    (CommAlgCat.algEquivOfIso eA).trans
      (affineSectionsAlgEquiv (Diagonalizable.algebra R M))
  let : Module.Projective R (AffineCoordinates.algebra G ⧸ I) :=
    Module.Projective.of_equiv eQ.symm.toLinearEquiv
  let : Algebra.FinitePresentation R (AddMonoidAlgebra R M) :=
    Diagonalizable.finitePresentation_groupAlgebra_of_fg R M
  let : Algebra.FinitePresentation R (AffineCoordinates.algebra G ⧸ I) :=
    Algebra.FinitePresentation.equiv eQ.symm
  have hIfg : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective
      (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mk_surjective)
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using h
  let J := subgroupNormalizerIdeal e I
  have hJfg : J.FG := subgroupNormalizerIdeal_fg e hIfg
  let hNcut := isCutOutBy_affineSubgroups_normalizer hI
  let emb := diagonalizableEmbedding e j'
  have hrange : emb.range = affineSubgroups (SubgroupFunctor.range j') := by
    funext A
    exact diagonalizableEmbedding_range e j' A
  have hlift : HasSquareZeroLifting
      (affineSubgroups (SubgroupFunctor.range j').normalizer) := by
    have h := hasSquareZeroLifting_normalizerFamily e emb
    have hfam : normalizerFamily emb.range =
        affineSubgroups (SubgroupFunctor.range j').normalizer := by
      funext A
      rw [hrange, affineSubgroups_normalizer hI]
    rwa [hfam] at h
  let : Algebra.FormallySmooth R (AffineCoordinates.algebra G ⧸ J) :=
    formallySmooth_of_hasSquareZeroLifting hNcut hlift
  let : Algebra.FinitePresentation R (AffineCoordinates.algebra G ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  let : Algebra.Smooth R (AffineCoordinates.algebra G ⧸ J) :=
    { finitePresentation := inferInstance
      formallySmooth := inferInstance }
  have hnormalizer : (SubgroupFunctor.range j').normalizer =
      (SubgroupFunctor.range j).normalizer.comap (AffineCoordinates.groupSchemeIso G).hom := by
    simpa only [j', AffineCoordinates.coordinateHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using SubgroupFunctor.normalizer_range_eq_comap_of_iso
        j' (AffineCoordinates.groupSchemeIso G)
  have hncoord : (SubgroupFunctor.range j').normalizer.IsRepresentedBy
      (AffineCoordinates.coordinateHom n) := by
    rw [hnormalizer]
    exact hnrep.comp_iso (AffineCoordinates.groupSchemeIso G).symm
  have hcutrep : (SubgroupFunctor.range j').normalizer.IsRepresentedBy (cutHom hNcut) :=
    isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_of_isCutOutBy hNcut)
  let eN : N ≅ cutGroupScheme hNcut := hncoord.isoOfIsRepresentedBy hcutrep
  exact smooth_of_over_iso ((Grp.forget _).mapIso eN) (smooth_cutGroupScheme hNcut)

/-- Smoothness is invariant under a choice of diagonalizable presentation. -/
theorem diagonalizableNormalizer_smooth_overSpec
    {R : CommRingCat.{u}} {G H N : GroupScheme (Spec R)}
    [IsAffine G.X.left] [Smooth G.X.hom]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    Smooth N.X.hom := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  let j := e'.inv ≫ i
  have hj : IsClosedSubgroup j := IsClosedSubgroup.iso_comp e'.symm hi
  have hrange : SubgroupFunctor.range j = SubgroupFunctor.range i :=
    SubgroupFunctor.range_iso_comp e'.symm i
  exact diagonalizableNormalizer_smooth_overRing j hj n (by rwa [hrange])

/-- Normalizers of closed diagonalizable subgroups in smooth relatively
affine groups are smooth over arbitrary bases. -/
theorem diagonalizableNormalizer_smooth
    {S : Scheme.{u}} {G H N : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    Smooth N.X.hom := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    S.affineOpenCover.openCover.changeProp (fun _ => inferInstance)
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  have hnbase : (SubgroupFunctor.range (B.map i)).normalizer.IsRepresentedBy (B.map n) := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hnrep.baseChange b
  exact diagonalizableNormalizer_smooth_overSpec (R := S.affineOpenCover.X k)
    (B.map i) (hH.baseChange b) (hi.baseChange b) (B.map n) hnbase

/-- Every representative of the normalizer of a closed multiplicative-type
subgroup of a smooth relatively affine group is smooth. -/
theorem relativeMultiplicativeTypeNormalizer_smooth
    {S : Scheme.{u}} {G H N : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    Smooth N.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  let : MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage S := 𝒰
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
  intro a
  let b := 𝒱.f a
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hnbase : (SubgroupFunctor.range (B.map i)).normalizer.IsRepresentedBy (B.map n) := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hnrep.baseChange b
  exact diagonalizableNormalizer_smooth
    (B.map i) (h𝒰 a) (hi.baseChange b) (B.map n) hnbase

/-- Choose an actual smooth closed normalizer of a multiplicative-type subgroup. -/
def relativeMultiplicativeTypeSmoothNormalizerModel
    {S : Scheme.{u}} {G H : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hi : IsClosedSubgroup i) :
    Σ N : GroupScheme S, {n : N ⟶ G // IsClosedSubgroup n ∧ Smooth N.X.hom ∧
      (SubgroupFunctor.range i).normalizer.IsRepresentedBy n} := by
  let N := RelativeMultiplicativeType.normalizerGroupScheme i hH hi
  let n : N ⟶ G := RelativeMultiplicativeType.normalizerHom i hH hi
  have hn := RelativeMultiplicativeType.normalizerHom_spec i hH hi
  exact ⟨N, n, hn.1,
    relativeMultiplicativeTypeNormalizer_smooth i hH hi n hn.2, hn.2⟩

end Langlands.GroupScheme
