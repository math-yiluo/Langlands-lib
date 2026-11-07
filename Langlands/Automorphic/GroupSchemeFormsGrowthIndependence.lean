import Langlands.Automorphic.GroupSchemeAdelicGrowthIndependenceProof
import Langlands.Automorphic.GroupSchemeTensorCuspidalL2

/-! # Embedding independence of the original automorphic and cuspidal form spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N M d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (sigma : MatrixRepresentation G (Fin M))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hsigma : IsClosedSubgroup sigma)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N) (hM : 0 < M)

/-- The original compact-finite, center-finite full-growth forms agree. -/
theorem adelicAutomorphicSubrepresentation_eq_of_closedImmersions :
    adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN =
      adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM := by
  ext f
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN) ↔
    f ∈ adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM
  rw [mem_adelicAutomorphicSubrepresentation, mem_adelicAutomorphicSubrepresentation]
  exact and_congr Iff.rfl (and_congr Iff.rfl ((closedImmersionAdelicGrowthIndependence F G N M rho sigma hN hM hrho hsigma).1 f.val).1)

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def adelicAutomorphicChangeRepresentation :
    (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (adelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM))

@[simp]
theorem adelicAutomorphicChangeRepresentation_val
    (f : (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    (adelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem adelicAutomorphicChangeRepresentation_symm_val
    (f : (adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule) :
    ((adelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (adelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem adelicAutomorphicChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    adelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM
        ((adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation c f) =
      (adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toRepresentation c
        (adelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f) := by
  apply Subtype.ext
  rw [adelicAutomorphicChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (adelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val
  rw [adelicAutomorphicChangeRepresentation_val]

/-- Uniform full growth imposes the same subrepresentation for the fixed differential action. -/
theorem uniformAdelicAutomorphicSubrepresentation_eq_of_closedImmersions :
    uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN =
      uniformAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM := by
  ext f
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f) ↔
      (f ∈ adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM ∧
        HasAdelicUniformPolynomialGrowth F G sigma hsmooth hcalc f)
  exact and_congr
    (by rw [adelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM])
    ((closedImmersionAdelicGrowthIndependence F G N M rho sigma hN hM hrho hsigma).2 d hsmooth hcalc f).2

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def uniformAdelicAutomorphicChangeRepresentation :
    (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (uniformAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (uniformAdelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM))

@[simp]
theorem uniformAdelicAutomorphicChangeRepresentation_val
    (f : (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    (uniformAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem uniformAdelicAutomorphicChangeRepresentation_symm_val
    (f : (uniformAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule) :
    ((uniformAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (uniformAdelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem uniformAdelicAutomorphicChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    uniformAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM
        ((uniformAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation c f) =
      (uniformAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toRepresentation c
        (uniformAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f) := by
  apply Subtype.ext
  rw [uniformAdelicAutomorphicChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (uniformAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val
  rw [uniformAdelicAutomorphicChangeRepresentation_val]

/-- Literal algebraic tensor membership is unchanged when the embedding changes. -/
theorem tensorAdelicAutomorphicSubrepresentation_eq_of_closedImmersions :
    tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN =
      tensorAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM := by
  ext f
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ tensorSmoothSubrepresentation F G) ↔
      (f ∈ adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM ∧
        f.val ∈ tensorSmoothSubrepresentation F G)
  exact and_congr
    (by rw [adelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM]) Iff.rfl

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def tensorAdelicAutomorphicChangeRepresentation :
    (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (tensorAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (tensorAdelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM))

@[simp]
theorem tensorAdelicAutomorphicChangeRepresentation_val
    (f : (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    (tensorAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem tensorAdelicAutomorphicChangeRepresentation_symm_val
    (f : (tensorAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toSubmodule) :
    ((tensorAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (tensorAdelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem tensorAdelicAutomorphicChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule) :
    tensorAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM
        ((tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation c f) =
      (tensorAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM).toRepresentation c
        (tensorAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f) := by
  apply Subtype.ext
  rw [tensorAdelicAutomorphicChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (tensorAdelicAutomorphicChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM f).val
  rw [tensorAdelicAutomorphicChangeRepresentation_val]

section Cuspidal

variable [LocallyOfFiniteType G.X.hom] (hPD : ParabolicDynamicStatement.{u})

/-- All original normalized proper-parabolic vanishing conditions remain identical. -/
theorem adelicCuspidalSubrepresentation_eq_of_closedImmersions :
    adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN =
      adelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM := by
  ext f
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) ↔
      (f ∈ adelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM ∧
        f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG)
  exact and_congr
    (by rw [adelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM]) Iff.rfl

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def adelicCuspidalChangeRepresentation :
    (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (adelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (adelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD))

@[simp]
theorem adelicCuspidalChangeRepresentation_val
    (f : (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    (adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem adelicCuspidalChangeRepresentation_symm_val
    (f : (adelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule) :
    ((adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (adelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem adelicCuspidalChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD
        ((adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toRepresentation c f) =
      (adelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toRepresentation c
        (adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f) := by
  apply Subtype.ext
  rw [adelicCuspidalChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val
  rw [adelicCuspidalChangeRepresentation_val]

/-- The uniform refinement of the original cusp space is embedding independent. -/
theorem uniformAdelicCuspidalSubrepresentation_eq_of_closedImmersions :
    uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN =
      uniformAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM := by
  ext f
  change (f ∈ adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN ∧
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f) ↔
      (f ∈ adelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM ∧
        HasAdelicUniformPolynomialGrowth F G sigma hsmooth hcalc f)
  exact and_congr
    (by rw [adelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD])
    ((closedImmersionAdelicGrowthIndependence F G N M rho sigma hN hM hrho hsigma).2 d hsmooth hcalc f).2

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def uniformAdelicCuspidalChangeRepresentation :
    (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (uniformAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (uniformAdelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD))

@[simp]
theorem uniformAdelicCuspidalChangeRepresentation_val
    (f : (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    (uniformAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem uniformAdelicCuspidalChangeRepresentation_symm_val
    (f : (uniformAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule) :
    ((uniformAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (uniformAdelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem uniformAdelicCuspidalChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    uniformAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD
        ((uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toRepresentation c f) =
      (uniformAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toRepresentation c
        (uniformAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f) := by
  apply Subtype.ext
  rw [uniformAdelicCuspidalChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (uniformAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val
  rw [uniformAdelicCuspidalChangeRepresentation_val]

/-- The literal tensor-smooth cusp subrepresentation is embedding independent. -/
theorem tensorAdelicCuspidalSubrepresentation_eq_of_closedImmersions :
    tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN =
      tensorAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM := by
  ext f
  change (f ∈ tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) ↔
      (f ∈ tensorAdelicAutomorphicSubrepresentation F G Kinf sigma hsmooth hcalc hG hsigma hK hM ∧
        f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG)
  exact and_congr
    (by rw [tensorAdelicAutomorphicSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM]) Iff.rfl

/-- Change of embedding is the identity on the original finite plot-smooth function. -/
def tensorAdelicCuspidalChangeRepresentation :
    (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule ≃ₗ[ℂ]
      (tensorAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (tensorAdelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD))

@[simp]
theorem tensorAdelicCuspidalChangeRepresentation_val
    (f : (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    (tensorAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem tensorAdelicCuspidalChangeRepresentation_symm_val
    (f : (tensorAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule) :
    ((tensorAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (tensorAdelicCuspidalSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD)).symm f

/-- The comparison intertwines the existing positive finite right translations. -/
theorem tensorAdelicCuspidalChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) :
    tensorAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD
        ((tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toRepresentation c f) =
      (tensorAdelicCuspidalSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toRepresentation c
        (tensorAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f) := by
  apply Subtype.ext
  rw [tensorAdelicCuspidalChangeRepresentation_val]
  change finitePlotSmoothFiniteRightAction F G c f.val =
    finitePlotSmoothFiniteRightAction F G c
      (tensorAdelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD f).val
  rw [tensorAdelicCuspidalChangeRepresentation_val]

end Cuspidal

end Langlands.Automorphic.GroupSchemeFunctions
