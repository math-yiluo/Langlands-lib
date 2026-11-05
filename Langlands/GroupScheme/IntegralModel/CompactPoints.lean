import Langlands.GroupScheme.IntegralModel.CoefficientPoints
import Langlands.AlgebraicGeometry.PointTopology.CompactPointProofs

/-! # Compact images of actual integral model sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Generic

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

private instance modelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

private instance modelGenericAffine : IsAffine M.genericFibre.X.left := by
  change IsAffine (pullback M.group.X.hom (Spec.algebraMap R K))
  infer_instance

variable [IsAffine G.X.left] [TopologicalSpace R] [TopologicalSpace K]
  [IsTopologicalRing K]

local instance sectionTopology : TopologicalSpace M.integralSections :=
  rationalPointTopology R M.group.X

local instance compactGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology K G.X

local instance modelIntegralAffineTopology :
    TopologicalSpace (M.group.affinePoints (CommAlgCat.of R R)) :=
  M.group.affinePointsTopologicalSpace _

local instance modelFieldAffineTopology :
    TopologicalSpace (M.group.affinePoints (CommAlgCat.of R K)) :=
  M.group.affinePointsTopologicalSpace _

local instance modelGenericAffineTopology :
    TopologicalSpace (M.genericFibre.affinePoints (CommAlgCat.of K K)) :=
  M.genericFibre.affinePointsTopologicalSpace _

local instance givenGenericAffineTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of K K)) :=
  G.affinePointsTopologicalSpace _

omit [IsTopologicalRing K] in
/-- The integral-point map is the canonical coefficient extension followed by the
actual generic-fibre comparison and the supplied generic isomorphism. -/
theorem integralPointMap_eq_affine (x : M.integralSections) :
    rationalPointsAffineHomeomorph G (M.integralPointMap x) =
      M.genericFibre.affinePointsTarget M.genericIso.hom (CommAlgCat.of K K)
        (affinePointsBaseChangeMulEquiv R K K M.group
          (M.group.affinePointMap (CommAlgCat.ofHom (Algebra.ofId R K))
            (rationalPointsAffineHomeomorph M.group x))) := by
  apply Over.OverMorphism.ext
  rw [rationalPointsAffineHomeomorph_left G]
  change (M.integralPointMap x).left =
    (affinePointsBaseChangeMulEquiv R K K M.group
      (M.group.affinePointMap (CommAlgCat.ofHom (Algebra.ofId R K))
        (rationalPointsAffineHomeomorph M.group x))).left ≫
      M.genericIso.hom.hom.hom.left
  rw [integralPointMap_left]
  apply congrArg (fun a => a ≫ M.genericIso.hom.hom.hom.left)
  apply pullback.hom_ext
  · rw [pullback.lift_fst, affinePointsBaseChangeMulEquiv_eq_ringPoint,
      ringPointBaseChangeEquiv_left_fst, affinePointMap_apply, Over.comp_left,
      rationalPointsAffineHomeomorph_left]
    rfl
  · rw [pullback.lift_snd, affinePointsBaseChangeMulEquiv_eq_ringPoint,
      ringPointBaseChangeEquiv_left_snd]
    simp [Spec.algebraMap]

/-- Continuity uses the canonical evaluation topologies on both actual point groups. -/
theorem continuous_integralPointMap (hRK : Continuous (algebraMap R K)) :
    Continuous M.integralPointMap := by
  have hmap := M.group.continuous_affinePointMap
    (CommAlgCat.ofHom (Algebra.ofId R K)) hRK
  have h :=
    (rationalPointsAffineHomeomorph G).symm.continuous.comp
      ((M.genericFibre.continuous_affinePointsTarget (CommAlgCat.of K K)
        M.genericIso.hom).comp
        ((affinePointsBaseChangeContinuousMulEquiv R K K M.group).continuous.comp
          (hmap.comp (rationalPointsAffineHomeomorph M.group).continuous)))
  convert h using 1
  funext x
  apply (rationalPointsAffineHomeomorph G).injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  change rationalPointsAffineHomeomorph G (M.integralPointMap x) =
    M.genericFibre.affinePointsTarget M.genericIso.hom (CommAlgCat.of K K)
      (affinePointsBaseChangeMulEquiv R K K M.group
        (M.group.affinePointMap (CommAlgCat.ofHom (Algebra.ofId R K))
          (rationalPointsAffineHomeomorph M.group x)))
  exact M.integralPointMap_eq_affine x

/-- The original generic-point evaluation, bundled as a continuous homomorphism. -/
def integralPointContinuousHom (hRK : Continuous (algebraMap R K)) :
    M.integralSections →ₜ* rationalPoints G where
  toMonoidHom := M.integralPointMap
  continuous_toFun := M.continuous_integralPointMap hRK

@[simp] theorem integralPointContinuousHom_apply
    (hRK : Continuous (algebraMap R K)) (x : M.integralSections) :
    M.integralPointContinuousHom hRK x = M.integralPointMap x := rfl

variable [IsTopologicalRing R] [T2Space R] [CompactSpace R]

omit [IsAffine G.X.left] [TopologicalSpace K] [IsTopologicalRing K] in
/-- Integral sections of the supplied finite-type affine model form a compact space. -/
theorem compactSpace_integralSections : CompactSpace M.integralSections := by
  let : CompactSpace (RingPoint R M.group.X R) :=
    affineSchemeCompactness_proof R R M.group.X
  exact (rationalPointHomeomorph R M.group.X).isClosedEmbedding.compactSpace

/-- A supplied integral model over a compact Hausdorff ring has compact generic image. -/
theorem isCompact_integralPoints (hRK : Continuous (algebraMap R K)) :
    IsCompact (M.integralPoints : Set (rationalPoints G)) := by
  let := M.compactSpace_integralSections
  exact isCompact_range (M.continuous_integralPointMap hRK)

end Generic

section Coefficient

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {R : Type u} [CommRing R] [IsDomain R] [Algebra R L] [IsFractionRing R L]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  (M : IntegralModel R L (baseChanged k L G))
  [TopologicalSpace R] [TopologicalSpace L] [IsTopologicalRing L]

private instance coefficientGenericAffine : IsAffine (baseChanged k L G).X.left := by
  change IsAffine (pullback G.X.hom (baseMap k L))
  infer_instance

local instance coefficientSectionTopology : TopologicalSpace M.integralSections :=
  rationalPointTopology R M.group.X

local instance originalCoefficientTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k L)) :=
  G.affinePointsTopologicalSpace _

local instance coefficientGenericRationalTopology :
    TopologicalSpace (rationalPoints (baseChanged k L G)) :=
  rationalPointTopology L (baseChanged k L G).X

/-- The section map into the original coefficient-point group is continuous. -/
theorem continuous_coefficientPointMap (hRL : Continuous (algebraMap R L)) :
    Continuous (M.coefficientPointMap k L) :=
  (baseChangeCoeffContinuousMulEquiv k L G).continuous.comp
    (M.continuous_integralPointMap hRL)

variable [IsTopologicalRing R] [T2Space R] [CompactSpace R]

/-- Compactness holds on the original group's actual coefficient-point carrier. -/
theorem isCompact_coefficientIntegralPoints (hRL : Continuous (algebraMap R L)) :
    IsCompact (M.coefficientIntegralPoints k L :
      Set (G.affinePoints (CommAlgCat.of k L))) :=
  (M.isCompact_coefficientIntegralPoints_iff k L).mpr (M.isCompact_integralPoints hRL)

end Coefficient

end Langlands.GroupScheme.IntegralModel
