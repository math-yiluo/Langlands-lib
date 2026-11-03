import Langlands.GroupScheme.Rational.TorusNormalizerStatement
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Torus.NormalizerLifting
import Langlands.GroupScheme.Torus.CentralizerSmooth

/-! # Smooth closed normalizers and centralizers of split tori

Proof of `TorusNormalizerRepresentableStatement`. For a split subtorus `i` of a connected
reductive group `G` over a field, the all-test normalizer and centralizer of `i` are represented
by the closed subgroups cut out by `subgroupNormalizerIdeal` and `subgroupCentralizerIdeal` in
the coordinate algebra of `G`. They are smooth because their algebra points lift along
square-zero extensions.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Corepresented CharacterAction

/-- **Normalizer and centralizer of a split torus are smooth closed subgroups**
(Milne 1.83, 1.92 and 13.10). -/
theorem torusNormalizerRepresentable : TorusNormalizerRepresentableStatement.{u} := by
  intro k _ G hG T i hi
  obtain ⟨⟨I, _, ⟨eT⟩⟩, hclosed⟩ := hi
  classical
  have := Fintype.ofFinite I
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hclosed
  have : Algebra.Smooth k (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G hG.smooth
  let e := AffineCoordinates.corepresentation G
  obtain ⟨J, hJ⟩ := exists_ideal_range (AffineCoordinates.coordinateHom i)
  let dT : (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp ≅ T.toGrp :=
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
  refine ⟨⟨_, _, AffineCoordinates.isClosedSubgroup_normalizer_range hJ, ?_,
      AffineCoordinates.isRepresentedBy_normalizer_range hJ⟩,
    torusCentralizer_hasSmoothClosedRepresentative i ⟨⟨I, inferInstance, ⟨eT⟩⟩, hclosed⟩ hG.smooth⟩
  have : Algebra.FormallySmooth k
      (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    formallySmooth_of_hasSquareZeroLifting (isCutOutBy_affineSubgroups_normalizer hJ) hN
  have : Algebra.FinitePresentation k
      (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    finitePresentation_quotient (R := CommRingCat.of k) (B := AffineCoordinates.algebra G) _
  have : Algebra.Smooth k (AffineCoordinates.algebra G ⧸ subgroupNormalizerIdeal e J) :=
    ⟨inferInstance, inferInstance⟩
  exact smooth_cutGroupScheme _

end Langlands.GroupScheme
