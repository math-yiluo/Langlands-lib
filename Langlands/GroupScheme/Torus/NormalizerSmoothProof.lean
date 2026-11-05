import Langlands.GroupScheme.Torus.NormalizerSmoothStatement
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smooth closed normalizers of arbitrary field tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Corepresented CharacterAction

/-- The split normalizer argument requires only a smooth affine ambient group. -/
theorem normalizer_hasSmoothClosedRepresentative_of_isSplitTorus
    {k : Type u} [Field k]
    {G T : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : T ⟶ G) (hT : IsSplitTorus T) (hclosed : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasSmoothClosedRepresentative := by
  obtain ⟨I, _, ⟨eT⟩⟩ := hT
  classical
  have := Fintype.ofFinite I
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hclosed
  have : Algebra.Smooth k (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G (inferInstance : Smooth G.X.hom)
  let e := AffineCoordinates.corepresentation G
  obtain ⟨J, hJ⟩ := exists_ideal_range (AffineCoordinates.coordinateHom i)
  let dT : (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp ≅ T :=
    Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)) ≪≫ eT.symm
  let jD := dT.hom ≫ AffineCoordinates.coordinateHom i
  have : Mono jD.hom.hom := by
    have : IsClosedImmersion jD.hom.hom.left :=
      IsClosedSubgroup.iso_comp dT (i := AffineCoordinates.coordinateHom i)
        (inferInstance : IsClosedImmersion (AffineCoordinates.coordinateHom i).hom.hom.left)
    exact Over.mono_of_mono_left _
  let emb := diagonalizableEmbedding e jD
  have hrange : ∀ A, emb.range A =
      affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom i)) A := by
    intro A
    rw [diagonalizableEmbedding_range, SubgroupFunctor.range_iso_comp]
  have hN : HasSquareZeroLifting
      (affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom i)).normalizer) := by
    have h := hasSquareZeroLifting_normalizerFamily e emb
    have hfam : normalizerFamily emb.range =
        affineSubgroups (SubgroupFunctor.range (AffineCoordinates.coordinateHom i)).normalizer := by
      funext A
      rw [affineSubgroups_normalizer hJ, funext hrange]
    rwa [hfam] at h
  refine ⟨_, _, AffineCoordinates.isClosedSubgroup_normalizer_range hJ, ?_,
    AffineCoordinates.isRepresentedBy_normalizer_range hJ⟩
  have : Algebra.FormallySmooth k
      (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    formallySmooth_of_hasSquareZeroLifting (isCutOutBy_affineSubgroups_normalizer hJ) hN
  have : Algebra.FinitePresentation k
      (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    finitePresentation_quotient (R := CommRingCat.of k) (B := AffineCoordinates.algebra G) _
  have : Algebra.Smooth k (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    ⟨inferInstance, inferInstance⟩
  exact smooth_cutGroupScheme _


/-- Every closed field torus has a smooth closed all-test normalizer in every
smooth affine ambient group. -/
theorem torusNormalizerSmoothClosed : TorusNormalizerSmoothClosedStatement.{u} := by
  intro k _ G _ _ T i hT hi
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, j, hj, hrep⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range i hi).1
  obtain ⟨K, hK, hA, hsplit⟩ := hT
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hfpqc := fieldExtension_fpqc k K
  have : Surjective b := hfpqc.1
  have : Flat b := hfpqc.2.1
  have : QuasiCompact b := hfpqc.2.2
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  obtain ⟨N', j', _, hsmooth, hrep'⟩ :=
    normalizer_hasSmoothClosedRepresentative_of_isSplitTorus
      ((GroupScheme.baseChange b).map i) hsplit (hi.baseChange b)
  have hrepb : ((SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).normalizer).IsRepresentedBy
       ((GroupScheme.baseChange b).map j) := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hrep.baseChange b
  have hsmoothb : Smooth ((GroupScheme.baseChange b).obj N).X.hom :=
    smooth_of_over_iso
      ((Grp.forget _).mapIso (hrepb.isoOfIsRepresentedBy hrep')) hsmooth
  refine ⟨N, j, hj, ?_, hrep⟩
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := N.X.hom) (g := b) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsmoothb

end Langlands.GroupScheme
