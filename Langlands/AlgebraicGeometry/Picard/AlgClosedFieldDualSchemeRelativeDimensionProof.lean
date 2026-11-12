import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionReduction
import Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof

/-! # Relative dimension of the chosen dual over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard DualOriginDimension
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `K` be algebraically closed. Assume that the Mumford family is Picard-zero and that
ample line bundles exist on abelian varieties over algebraically closed fields. Then the stalk
of the chosen dual of an abelian variety of dimension `g` at its rational origin has Krull
dimension at least `g`. Local finite type of the dual is supplied by
`dualScheme_locallyOfFiniteType`. -/
theorem algClosedFieldDualOriginDimensionLowerBound_of_mumford_ample
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ)
    (hg : A.HasRelativeDimension g) :
    (g : WithBot ℕ∞) ≤ ringKrullDim ((dualScheme A hA).left.presheaf.stalk
      ((dualOrigin A hA).left (IsLocalRing.closedPoint K))) := by
  have : LocallyOfFiniteType (dualScheme A hA).hom := dualScheme_locallyOfFiniteType A hA
  obtain ⟨L, hL⟩ := ample K A.toGrp inferInstance inferInstance inferInstance
  have hfin := algClosedFieldAmpleTranslationStabilizerFinite K A L hL
  rw [← fieldSmoothClosedPointStalkDimension K A.X.left A.X.hom g hg _
    (PicardOriginDimension.isClosed_unit K A), ← dualClassifier_unit mumford K A hA L]
  exact quasiFiniteAtStalkDimension _ _ _ (locallyOfFiniteType_dualClassifier mumford K A hA L) _
    (quasiFiniteAt_dualClassifier mumford K A hA L hfin)

/-- Let `K` be algebraically closed. Assume that the Mumford family is Picard-zero and that
ample line bundles exist on abelian varieties over algebraically closed fields. Then the chosen
dual of an abelian scheme of relative dimension `g` over `Spec K` is smooth of relative
dimension `g`. Local finite presentation of the dual is supplied by
`dualScheme_locallyOfFinitePresentation`. -/
theorem algClosedFieldDualSchemeRelativeDimension_of_mumford_ample
    (mumford : MumfordBundlePicardZeroStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}) :
    AlgClosedFieldDualSchemeRelativeDimensionStatement.{u} := by
  intro K _ _ A hA g hg
  have : LocallyOfFinitePresentation (dualScheme A hA).hom :=
    dualScheme_locallyOfFinitePresentation A hA
  obtain ⟨_⟩ := nonempty_grpObj_dualScheme A hA
  let D := dualScheme A hA
  let e := dualOrigin A hA
  obtain ⟨-, hcot, hreg⟩ :=
    Langlands.Scheme.fieldPointTangentLocalRegularity K D e inferInstance
  obtain ⟨τ⟩ := dualSchemeTangentH1 A hA
  obtain ⟨-, hHg⟩ := fieldStructureSheafH1DimensionBound K A g hg
  have hT : Module.finrank K (Langlands.Scheme.tangentSpaceAtPoint D e) ≤ g :=
    τ.finrank_eq ▸ hHg
  have hlow := algClosedFieldDualOriginDimensionLowerBound_of_mumford_ample mumford ample
    K A hA g hg
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

/-- Over an algebraically closed field `K`, the chosen dual of an abelian scheme of relative
dimension `g` over `Spec K` is smooth of relative dimension `g`. The two inputs of
`algClosedFieldDualSchemeRelativeDimension_of_mumford_ample` are the published theorems
`mumfordBundlePicardZero` and `GroupScheme.algebraicallyClosedFieldAmpleExistence`. -/
theorem algClosedFieldDualSchemeRelativeDimension :
    AlgClosedFieldDualSchemeRelativeDimensionStatement.{u} :=
  algClosedFieldDualSchemeRelativeDimension_of_mumford_ample mumfordBundlePicardZero
    GroupScheme.algebraicallyClosedFieldAmpleExistence

end Langlands.AbelianScheme
