import Langlands.BruhatTits.RationalPoints.DenseBoundedNormalizerAdjointStatement
import Langlands.BruhatTits.RationalPoints.AdjointImageBoundedTransfer
import Langlands.GroupScheme.MatrixRepresentation.ConjugationKernel
import Langlands.GroupScheme.MatrixRepresentation.ConjugationBounded
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Bounded adjoint images of dense bounded subgroup normalizers -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.MatrixRepresentation
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

set_option linter.defProp false in
/-- A dense bounded rational subgroup has bounded normalizer image in the
actual quotient by the full scheme center. -/
def denseBoundedNormalizerAdjoint : DenseBoundedNormalizerAdjointStatement.{u} := by
  intro F _ _ _ _ G hG A q hq
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field F _ G.X.hom
  let : IsAffineHom A.X.hom :=
    hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  intro H hHb hHd
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : Mono ρ.hom.hom := Over.mono_of_mono_left _
  let S := conjugationSubrepresentation ρ H hHd
  let : IsAffineHom
      (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  let : IsAffine
      (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X.left :=
    GeneralLinear.isAffine_groupScheme _ _
  let : Smooth
      (GeneralLinear.groupScheme (Fin S.dimension) (CommRingCat.of F)).X.hom :=
    GeneralLinear.smoothStatement _ _
  exact isAlgebraicallyBounded_adjoint_image_of_kernel_eq_center q hq
    S.representation (S.range_kernel_eq_center hHd)
    (Subgroup.normalizer (H : Set (rationalPoints G)) : Set (rationalPoints G))
    (S.isAlgebraicallyBounded_normalizer_image hHb)

end Langlands.BruhatTits.RationalPoints
