import Langlands.Representation.Category.ProjectiveGeneration
import Langlands.Representation.CuspidalSupport.RationalUniversalProjectivity
import Langlands.Representation.CuspidalSupport.RationalUniversalQuotients

/-! Faithful integer Hom for the actual full-restriction norm-kernel induction. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.CategoryTheory.Renard
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalGenerationTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalGenerationTopologicalGroup : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- The actual compact induction maps nontrivially to every irreducible object
in the unramified orbit of the lifted base. -/
theorem exists_nonzero_rationalNormKernel_to_irreducible
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (hD : D.IsIrreducible)
    (h : IsRationalInertiaRelated G (rationalInertiaBaseLift G π) D) :
    ∃ q : rationalNormKernelCompactInduction G π ⟶ D, q ≠ 0 := by
  let := hD
  let : Nontrivial D := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GroupScheme.rationalPoints G)) D.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  let q := rationalNormKernelInertiaQuotient G π D h
  obtain ⟨w, hw⟩ := rationalNormKernelInertiaQuotient_surjective G π D h v
  refine ⟨q, fun hq => ?_⟩
  have hz := congrArg (fun a => SmoothRep.hom a w) hq
  change SmoothRep.hom q w = 0 at hz
  exact hv (hw.symm.trans hz)

/-- Membership and compact coefficients of the entire norm-kernel restriction
make the actual integer-module-valued block Hom functor faithful. -/
theorem rationalNormKernelHom_faithful
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype)) :
    (preadditiveCoyonedaInt (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π))).Faithful := by
  let := rationalNormKernelCompactInduction_projective G π hc
  apply SmoothRep.faithful_preadditiveCoyonedaInt_of_projective_subquotients
  intro Y D hD hDY
  exact exists_nonzero_rationalNormKernel_to_irreducible G π D hD
    (Y.property D hD hDY)

/-- Choose a block morphism out of the actual induction detecting a nonzero
block morphism, under explicit membership and compact-restriction hypotheses. -/
def rationalNormKernelBlockDetector
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    {X Y : RationalInertiaBlock G (rationalInertiaBaseLift G π)}
    (d : X ⟶ Y) (hd : d ≠ 0) :
    (⟨rationalNormKernelCompactInduction G π, hmem⟩ :
      RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ X := by
  let := rationalNormKernelCompactInduction_projective G π hc
  have hd' : d.hom ≠ 0 := fun h => hd (ObjectProperty.hom_ext _ h)
  exact ObjectProperty.homMk (SmoothRep.projectiveSubquotientDetector
    (rationalNormKernelCompactInduction G π) d.hom hd'
    (fun D hD hDY => exists_nonzero_rationalNormKernel_to_irreducible G π D hD
      (Y.property D hD hDY)))

/-- The chosen block detector has a nonzero composite with the original map. -/
theorem rationalNormKernelBlockDetector_comp_ne_zero
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (rationalCommonNormKernel G).subtype))
    {X Y : RationalInertiaBlock G (rationalInertiaBaseLift G π)}
    (d : X ⟶ Y) (hd : d ≠ 0) :
    rationalNormKernelBlockDetector G π hmem hc d hd ≫ d ≠ 0 := by
  let := rationalNormKernelCompactInduction_projective G π hc
  intro h
  exact SmoothRep.projectiveSubquotientDetector_comp_ne_zero
    (rationalNormKernelCompactInduction G π) d.hom
    (fun h => hd (ObjectProperty.hom_ext _ h))
    (fun D hD hDY => exists_nonzero_rationalNormKernel_to_irreducible G π D hD
      (Y.property D hD hDY)) (congrArg (fun a => a.hom) h)

end Langlands.CuspidalSupport
