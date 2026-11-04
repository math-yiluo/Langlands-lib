import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Group.HaarModulus
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! # Haar scaling on a rational dynamic unipotent subgroup is the adjoint determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Over a nonarchimedean local field `k`, let `χ` be a cocharacter of a connected reductive
group `G`. For a rational point `m` of the centralizer `Z(χ)`, the factor by which conjugation
`u ↦ m u m⁻¹` scales Haar measure on the closed subgroup `U(χ)(k)` of `G(k)` is the normalized
absolute value of `det(Ad m | Lie U(χ))`, namely Mathlib's Haar scaling factor
`distribHaarChar k` of multiplication by that determinant on `k`. This is a proof target. -/
def DynamicUnipotentHaarDeterminantStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
      (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X)))
      (m : rationalPoints Z)
      (hm : m ≫ iZ.hom.hom ∈ Subgroup.normalizer
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))),
      (HaarModulus.closedNormalizerCharacter _ hUc ⟨m ≫ iZ.hom.hom, hm⟩ : ℝ≥0) =
        MeasureTheory.distribHaarChar k
          (rationalCharacterEval
            ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m)

end Langlands.Aubert.General.RationalPointFamily
