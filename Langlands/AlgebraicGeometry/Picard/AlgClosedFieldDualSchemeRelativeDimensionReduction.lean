import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationStatement
import Langlands.AlgebraicGeometry.FieldGroupSchemeHomogeneity
import Langlands.AlgebraicGeometry.Picard.DualGroupScheme
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityProof
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof
import Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothProof
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Langlands.AlgebraicGeometry.Picard.DualSchemeTangentH1
import Langlands.AlgebraicGeometry.Picard.DualOriginMumfordClassifier

/-! # Relative dimension of the chosen dual over an algebraically closed field, conditionally -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The chosen dual parameter scheme carries the group law of
`dualCommGroupSchemeFromEvaluation`, built from an inverse of the Poincaré family and the
published coherence theorems. -/
lemma nonempty_grpObj_dualScheme {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) : Nonempty (GrpObj (dualScheme A hA)) := by
  let X := (relativeSpace A.X.hom).obj (dualScheme A hA)
  let P : X.Modules := (poincareFamily A hA).obj.carrier
  have hP : Langlands.CategoryTheory.TensorInvertible P :=
    (locallyFreeRankOneIffTensorInvertible X P).mpr (poincareFamily A hA).property
  obtain ⟨N, ⟨e⟩⟩ := hP
  have hN : IsLocallyFreeRankOne N :=
    (locallyFreeRankOneIffTensorInvertible X N).mp ⟨P, ⟨(β_ N P) ≪≫ e⟩⟩
  let M : LineBundle X := ⟨N, hN⟩
  let evaluation : tensorObj P M.obj ≅ structureSheaf X :=
    (localizedTensorIso X P N).symm ≪≫ e
  let G := dualCommGroupSchemeFromEvaluation A hA pullbackTensorComparisonIsIso
    M evaluation picardZeroPullback pullbackTensorComposition pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
  exact ⟨G.toGrp.grp⟩

/-- Let `K` be algebraically closed. Assume local finite presentation of chosen duals, the
identification of the tangent space of the dual at its origin with `H¹(A, 𝒪_A)`, and the
lower bound `g ≤ dim 𝒪_{D, 0}` for the origin stalk. Then the chosen dual of an abelian
scheme of relative dimension `g` over `Spec K` is smooth of relative dimension `g`. -/
theorem algClosedFieldDualSchemeRelativeDimension_of
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (tangent : ∀ (k : Type u) [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))
      (hA : HasDualScheme A),
      Nonempty (Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA) ≃ₗ[k]
        (relativeCohomology A.X.hom 1).obj (structureSheaf A.X.left)))
    (lowerBound : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
      A.HasRelativeDimension g →
        (g : WithBot ℕ∞) ≤ ringKrullDim ((dualScheme A hA).left.presheaf.stalk
          ((dualOrigin A hA).left (IsLocalRing.closedPoint K)))) :
    AlgClosedFieldDualSchemeRelativeDimensionStatement.{u} := by
  intro K _ _ A hA g hg
  have : LocallyOfFinitePresentation (dualScheme A hA).hom :=
    finitePresentation (Spec (CommRingCat.of K)) A hA
  obtain ⟨_⟩ := nonempty_grpObj_dualScheme A hA
  let D := dualScheme A hA
  let e := dualOrigin A hA
  obtain ⟨-, hcot, hreg⟩ :=
    Langlands.Scheme.fieldPointTangentLocalRegularity K D e inferInstance
  obtain ⟨τ⟩ := tangent K A hA
  obtain ⟨-, hHg⟩ := fieldStructureSheafH1DimensionBound K A g hg
  have hT : Module.finrank K (Langlands.Scheme.tangentSpaceAtPoint D e) ≤ g :=
    τ.finrank_eq ▸ hHg
  have hlow := lowerBound K A hA g hg
  have hR := hreg g hT hlow
  have hdim : ringKrullDim (D.left.presheaf.stalk (e.left (IsLocalRing.closedPoint K))) = g := by
    refine le_antisymm ?_ hlow
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hR, ← hcot]
    exact_mod_cast hT
  have := IsRegularLocalRing.isDomain (D.left.presheaf.stalk (e.left (IsLocalRing.closedPoint K)))
  have hx₀ : IsClosed ({e.left (IsLocalRing.closedPoint K)} : Set D.left) :=
    (pointEquivClosedPoint D.hom ⟨e.left, Over.w e⟩).2
  have key (y : D.left) (hy : IsClosed ({y} : Set D.left)) :
      _root_.IsReduced (D.left.presheaf.stalk y) ∧
        ringKrullDim (D.left.presheaf.stalk y) = g := by
    obtain ⟨α, -, rfl⟩ := Langlands.AlgebraicGeometry.GrpObj.exists_iso_apply_closedPoint D _ y
      hx₀ hy
    let φ := (asIso (α.hom.stalkMap (e.left (IsLocalRing.closedPoint K)))).commRingCatIsoToRingEquiv
    exact ⟨isReduced_of_injective φ φ.injective, (ringKrullDim_eq_of_ringEquiv φ).trans hdim⟩
  have : JacobsonSpace D.left := LocallyOfFiniteType.jacobsonSpace D.hom
  have : IsReduced D.left :=
    Langlands.AlgebraicGeometry.isReduced_of_isReduced_stalk_closedPoint D.left
      fun y hy => (key y hy).1
  have : Smooth D.hom :=
    Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth K D.left D.hom
      fun x y hx hy => Langlands.AlgebraicGeometry.GrpObj.exists_iso_apply_closedPoint D x y hx hy
  exact Langlands.AlgebraicGeometry.smoothOfRelativeDimension_of_ringKrullDim_stalk D.hom g
    fun y hy => (key y hy).2

/-- Let `K` be algebraically closed. Assume local finite presentation of chosen duals,
Picard-zero membership of the Mumford family, and existence of ample line bundles on abelian
varieties over algebraically closed fields. Then the chosen dual of an abelian scheme of
relative dimension `g` over `Spec K` is smooth of relative dimension `g`. -/
theorem algClosedFieldDualSchemeRelativeDimension_of_inputs
    (finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u})
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}) :
    AlgClosedFieldDualSchemeRelativeDimensionStatement.{u} :=
  algClosedFieldDualSchemeRelativeDimension_of finitePresentation
    (fun _ _ A hA => dualSchemeTangentH1 A hA)
    (algClosedFieldDualOriginDimensionLowerBound_of mumford finitePresentation ample)

end Langlands.AbelianScheme
