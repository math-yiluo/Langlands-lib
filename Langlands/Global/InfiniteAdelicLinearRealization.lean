import Langlands.Geometry.Manifold.LinearLieGroup.Realization
import Langlands.Global.InfinitePlaceMatrixRealization
import Langlands.Global.InfinitePlaceRealizationSmooth
import Langlands.Global.ReductiveInfiniteAdelicManifold

/-!
# A closed linear realization of the archimedean points of a reductive group

For a connected reductive group scheme `G` over a number field `F`,
`Langlands.Global.InfiniteAdelicGroupPoints.exists_isClosedLinearRealization` gives `N` and a
homomorphism `ρ : InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ` that is a closed linear
realization (`Langlands.LinearLieGroup.IsClosedLinearRealization`) for the Library's atlas
`reductiveChartedSpace F G hG` with model `smoothModel F hG.smoothDimension`.

The homomorphism is `matrixRealization F G ρ`, a closed matrix representation of `G`
(`InfinitePlaceGroupPoints.exists_closedMatrixRealization`) on points over the infinite adele
ring, read in the mixed coordinates of `archimedeanGLCoordinates`. Smoothness in both directions
comes from the Library's criterion `reductive_contMDiff_iff_coordinateSmooth`, the general-linear
criterion `GeneralLinear.coordinateSmooth_iff_contMDiff`, and
`MatrixRepresentation.coordinateSmooth_of_postcomp`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The archimedean points of `G` in the units of `ArchimedeanMatrix F N`, through a matrix
representation `ρ` of `G`: `ρ` on points over the infinite adeles followed by
`archimedeanGLCoordinates`. -/
def matrixRealization {N : ℕ} (ρ : GroupScheme.MatrixRepresentation G (Fin N)) :
    InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ :=
  (archimedeanGLCoordinates F N).toMulEquiv.toMonoidHom.comp
    (ρ.affineMatrix (CommAlgCat.of F (InfiniteAdeleRing F)))

/-- `matrixRealization` is the representation in the mixed coefficient coordinates of
`GeneralLinear.coefficientCoordinates`. -/
theorem matrixRealization_eq {N : ℕ} (ρ : GroupScheme.MatrixRepresentation G (Fin N))
    (x : InfiniteAdelicGroupPoints F G) :
    matrixRealization F G ρ x =
      GroupScheme.GeneralLinear.coefficientCoordinates (Fin N) (CommRingCat.of F)
        (CommAlgCat.of F (InfiniteAdeleRing F)) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
        (x ≫ ρ.hom.hom) := rfl

/-- For a connected reductive `G` and a closed matrix representation `ρ`, `matrixRealization F G ρ`
is a closed linear realization of `G(F_∞)` with the Library's reductive atlas: a closed embedding
(`isClosedEmbedding_affineMatrix`), smooth by the coordinate-smooth criterion of the atlas, and
reflecting smoothness because a closed representation reflects coordinate smoothness. -/
theorem isClosedLinearRealization_matrixRealization
    (hG : GroupScheme.IsConnectedReductive G) {N : ℕ}
    (ρ : GroupScheme.MatrixRepresentation G (Fin N)) (hρ : GroupScheme.IsClosedSubgroup ρ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, smoothModel F hG.smoothDimension)
      (matrixRealization F G ρ) := by
  let := hG.affineScheme
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := reductiveChartedSpace F G hG
  have : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  refine ⟨?_, ?_, ?_⟩
  · exact (archimedeanGLCoordinates F N).toHomeomorph.isClosedEmbedding.comp
      (ρ.isClosedEmbedding_affineMatrix (CommAlgCat.of F (InfiniteAdeleRing F)) hρ)
  · have hid := (reductive_contMDiff_iff_coordinateSmooth F G hG
      𝓘(ℝ, smoothModel F hG.smoothDimension) id).1 contMDiff_id
    have h3 := (GroupScheme.GeneralLinear.coordinateSmooth_iff_contMDiff (Fin N)
      (CommRingCat.of F) (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      𝓘(ℝ, smoothModel F hG.smoothDimension) _).1 (hid.postcomp ρ.hom.hom)
    exact Units.contMDiff_val.comp h3
  · intro m p hp
    rw [reductive_contMDiff_iff_coordinateSmooth F G hG]
    apply ρ.coordinateSmooth_of_postcomp hρ (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    apply (GroupScheme.GeneralLinear.coordinateSmooth_iff_contMDiff (Fin N)
      (CommRingCat.of F) (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom 𝓘(ℝ, Fin m → ℝ) _).2
    exact LinearLieGroup.contMDiff_units_of_contDiff_val _ hp

/-- **The archimedean points of a reductive group have a closed linear realization**:
`G(F_∞)`, with the Library's atlas `reductiveChartedSpace`, admits a closed linear realization in
the units of `ArchimedeanMatrix F N` for some `N`. -/
theorem exists_isClosedLinearRealization (hG : GroupScheme.IsConnectedReductive G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    ∃ (N : ℕ) (ρ : InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ),
      LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, smoothModel F hG.smoothDimension) ρ := by
  obtain ⟨N, ρ, hρ, -⟩ := InfinitePlaceGroupPoints.exists_closedMatrixRealization G hG
  exact ⟨N, matrixRealization F G ρ, isClosedLinearRealization_matrixRealization F G hG ρ hρ⟩

end Langlands.Global.InfiniteAdelicGroupPoints
