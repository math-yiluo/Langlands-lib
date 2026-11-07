import Langlands.Automorphic.GroupSchemeAdelicGrowthIndependenceProof

/-! # Embedding independence of the existing full adelic growth spaces -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N M : ℕ}
  (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (sigma : Langlands.GroupScheme.MatrixRepresentation G (Fin M))
  (hN : 0 < N) (hM : 0 < M)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hsigma : Langlands.GroupScheme.IsClosedSubgroup sigma)

include hrho hsigma

/-- Two positive-rank closed embeddings give the same actual full-growth
subrepresentation in the original continuous rational-function carrier. -/
theorem adelicGrowthSubrepresentation_eq_of_closedImmersions :
    adelicGrowthSubrepresentation F G rho hN =
      adelicGrowthSubrepresentation F G sigma hM := by
  ext f
  change HasAdelicPolynomialGrowth F G rho f ↔ HasAdelicPolynomialGrowth F G sigma f
  exact ((closedImmersionAdelicGrowthIndependence
    F G N M rho sigma hN hM hrho hsigma).1 f).2

/-- The existing common-open-finite-stabilizer smooth intersection is independent
of the closed matrix embedding. -/
theorem finitePlotSmoothAdelicGrowthSubrepresentation_eq_of_closedImmersions :
    finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN =
      finitePlotSmoothAdelicGrowthSubrepresentation F G sigma hM := by
  unfold finitePlotSmoothAdelicGrowthSubrepresentation
  rw [adelicGrowthSubrepresentation_eq_of_closedImmersions
    F G rho sigma hN hM hrho hsigma]

/-- Changing the embedding is the identity on the original continuous functions. -/
def adelicGrowthChangeRepresentation :
    (adelicGrowthSubrepresentation F G rho hN).toSubmodule ≃ₗ[ℂ]
      (adelicGrowthSubrepresentation F G sigma hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (adelicGrowthSubrepresentation_eq_of_closedImmersions F G rho sigma hN hM hrho hsigma))

@[simp]
theorem adelicGrowthChangeRepresentation_val
    (f : (adelicGrowthSubrepresentation F G rho hN).toSubmodule) :
    (adelicGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem adelicGrowthChangeRepresentation_symm_val
    (f : (adelicGrowthSubrepresentation F G sigma hM).toSubmodule) :
    ((adelicGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma).symm f).val =
      f.val := rfl

/-- The equivalence intertwines the existing full adelic positive right action. -/
theorem adelicGrowthChangeRepresentation_rightAction
    (f : (adelicGrowthSubrepresentation F G rho hN).toSubmodule)
    (g : AdelicGroupPoints F G) :
    adelicGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma
        ((adelicGrowthSubrepresentation F G rho hN).toRepresentation g f) =
      (adelicGrowthSubrepresentation F G sigma hM).toRepresentation g
        (adelicGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma f) := by
  apply Subtype.ext
  rfl

/-- The smooth full-growth spaces are also identified by the original function. -/
def finitePlotSmoothAdelicGrowthChangeRepresentation :
    (finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN).toSubmodule ≃ₗ[ℂ]
      (finitePlotSmoothAdelicGrowthSubrepresentation F G sigma hM).toSubmodule :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (finitePlotSmoothAdelicGrowthSubrepresentation_eq_of_closedImmersions
      F G rho sigma hN hM hrho hsigma))

@[simp]
theorem finitePlotSmoothAdelicGrowthChangeRepresentation_val
    (f : (finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN).toSubmodule) :
    (finitePlotSmoothAdelicGrowthChangeRepresentation
      F G rho sigma hN hM hrho hsigma f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem finitePlotSmoothAdelicGrowthChangeRepresentation_symm_val
    (f : (finitePlotSmoothAdelicGrowthSubrepresentation F G sigma hM).toSubmodule) :
    ((finitePlotSmoothAdelicGrowthChangeRepresentation
      F G rho sigma hN hM hrho hsigma).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (finitePlotSmoothAdelicGrowthSubrepresentation_eq_of_closedImmersions
      F G rho sigma hN hM hrho hsigma)).symm f

theorem finitePlotSmoothAdelicGrowthChangeRepresentation_rightAction
    (f : (finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN).toSubmodule)
    (g : AdelicGroupPoints F G) :
    finitePlotSmoothAdelicGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma
        ((finitePlotSmoothAdelicGrowthSubrepresentation F G rho hN).toRepresentation g f) =
      (finitePlotSmoothAdelicGrowthSubrepresentation F G sigma hM).toRepresentation g
        (finitePlotSmoothAdelicGrowthChangeRepresentation
          F G rho sigma hN hM hrho hsigma f) := by
  apply Subtype.ext
  rw [finitePlotSmoothAdelicGrowthChangeRepresentation_val]
  change continuousRightAction F G g f.val = continuousRightAction F G g
    (finitePlotSmoothAdelicGrowthChangeRepresentation
      F G rho sigma hN hM hrho hsigma f).val
  rw [finitePlotSmoothAdelicGrowthChangeRepresentation_val]

section Uniform

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Uniform growth submodules coincide for the same actual enveloping action;
the imported theorem chooses the growth exponent before every derivative. -/
theorem adelicUniformGrowthSubmodule_eq_of_closedImmersions :
    adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN =
      adelicUniformGrowthSubmodule F G sigma hsmooth hcalc hM := by
  ext f
  change HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f ↔
    HasAdelicUniformPolynomialGrowth F G sigma hsmooth hcalc f
  exact ((closedImmersionAdelicGrowthIndependence
    F G N M rho sigma hN hM hrho hsigma).2 d hsmooth hcalc f).2

/-- Finite right translation is restricted to the same uniform-growth subspace. -/
theorem adelicUniformGrowthFiniteSubrepresentation_eq_of_closedImmersions :
    adelicUniformGrowthFiniteSubrepresentation F G rho hsmooth hcalc hN =
      adelicUniformGrowthFiniteSubrepresentation F G sigma hsmooth hcalc hM := by
  apply Subrepresentation.toSubmodule_injective
  exact adelicUniformGrowthSubmodule_eq_of_closedImmersions
    F G rho sigma hN hM hrho hsigma hsmooth hcalc

/-- The uniform comparison is the identity on the existing finite plot-smooth
carrier and keeps the smooth atlas and scalar commutator premise fixed. -/
def adelicUniformGrowthChangeRepresentation :
    adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN ≃ₗ[ℂ]
      adelicUniformGrowthSubmodule F G sigma hsmooth hcalc hM :=
  LinearEquiv.ofEq _ _ (adelicUniformGrowthSubmodule_eq_of_closedImmersions
    F G rho sigma hN hM hrho hsigma hsmooth hcalc)

@[simp]
theorem adelicUniformGrowthChangeRepresentation_val
    (f : adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN) :
    (adelicUniformGrowthChangeRepresentation
      F G rho sigma hN hM hrho hsigma hsmooth hcalc f).val = f.val := rfl

@[simp]
theorem adelicUniformGrowthChangeRepresentation_symm_val
    (f : adelicUniformGrowthSubmodule F G sigma hsmooth hcalc hM) :
    ((adelicUniformGrowthChangeRepresentation
      F G rho sigma hN hM hrho hsigma hsmooth hcalc).symm f).val = f.val := rfl

/-- The comparison intertwines positive finite right translation on the original
finite plot-smooth functions. -/
theorem adelicUniformGrowthChangeRepresentation_finiteRightAction
    (f : adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN)
    (c : FiniteAdelicGroupPoints F G) :
    adelicUniformGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma hsmooth hcalc
        ((adelicUniformGrowthFiniteSubrepresentation
          F G rho hsmooth hcalc hN).toRepresentation c f) =
      (adelicUniformGrowthFiniteSubrepresentation
        F G sigma hsmooth hcalc hM).toRepresentation c
          (adelicUniformGrowthChangeRepresentation
            F G rho sigma hN hM hrho hsigma hsmooth hcalc f) := by
  apply Subtype.ext
  rfl

/-- The same enveloping element acts on the same original smooth function
through either embedding-dependent realization of the uniform subspace. -/
theorem adelicUniformGrowthChangeRepresentation_envelopingAction
    (f : adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN)
    (a : AdelicEnvelopingAlgebra F G hsmooth) :
    adelicUniformGrowthChangeRepresentation F G rho sigma hN hM hrho hsigma hsmooth hcalc
        (adelicUniformGrowthEnvelopingAction F G rho hsmooth hcalc hN a f) =
      adelicUniformGrowthEnvelopingAction F G sigma hsmooth hcalc hM a
        (adelicUniformGrowthChangeRepresentation
          F G rho sigma hN hM hrho hsigma hsmooth hcalc f) := by
  apply Subtype.ext
  rfl

end Uniform

end Langlands.Automorphic.GroupSchemeFunctions
