import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Induction.SplitStagesComparison

/-! Generation of the actual inertia block by the full norm-kernel induction. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalQuotientsTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalQuotientsTopologicalGroup : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- On the complete norm kernel, every unramified twist of the lifted base has
exactly the original action, transported along the actual carrier lift. -/
def rationalNormKernelTwistRestrictionEquiv
    (χ : unramifiedCharacters (fun c => (rationalNormCharacters G c).toMul)) :
    Representation.Equiv (π.representation.comp (rationalCommonNormKernel G).subtype)
      ((rationalUnramifiedTwist G χ (rationalInertiaBaseLift G π)).representation.comp
        (rationalCommonNormKernel G).subtype) where
  toLinearEquiv := (SmoothRep.universeLiftEquiv.{uF} π).toLinearEquiv
  isIntertwining' k := by
    apply LinearMap.ext
    intro v
    change ULift.up (π.representation (k : GroupScheme.rationalPoints G) v) =
      (χ.val.toMonoidHom (k : GroupScheme.rationalPoints G) : ℂ) •
        ULift.up (π.representation (k : GroupScheme.rationalPoints G) v)
    have hk : χ.val.toMonoidHom (k : GroupScheme.rationalPoints G) = 1 :=
      χ.property k.property
    rw [hk]
    simp

/-- The actual full-restriction compact induction surjects onto every object
in the unramified orbit of the lifted base. No irreducibility is needed. -/
theorem exists_surjective_rationalNormKernelCompactInduction
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (h : IsRationalInertiaRelated G (rationalInertiaBaseLift G π) D) :
    ∃ q : rationalNormKernelCompactInduction G π ⟶ D,
      Function.Surjective (SmoothRep.hom q) := by
  obtain ⟨χ, ⟨e⟩⟩ := h
  let E := (rationalNormKernelTwistRestrictionEquiv G π χ).trans
    (Induction.restrictAlongEquiv (rationalCommonNormKernel G).subtype
      (SmoothRep.equivOfIso e.symm))
  let q : rationalNormKernelCompactInduction G π ⟶ D := SmoothRep.ofHom
    (Induction.cosetSum (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
      D.representation (π.representation.comp (rationalCommonNormKernel G).subtype)
      E.toIntertwiningMap)
  refine ⟨q, fun v => ?_⟩
  obtain ⟨w, hw⟩ := E.surjective v
  refine ⟨Induction.unitMap (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G)
    (π.representation.comp (rationalCommonNormKernel G).subtype)
    ((SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).isSmooth) w, ?_⟩
  exact (Induction.cosetSum_comp_unitMap (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G) D.representation
    (π.representation.comp (rationalCommonNormKernel G).subtype)
    ((SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).isSmooth)
    E.toIntertwiningMap w).trans hw

/-- A chosen actual quotient map onto an inertia-related object. -/
def rationalNormKernelInertiaQuotient
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (h : IsRationalInertiaRelated G (rationalInertiaBaseLift G π) D) :
    rationalNormKernelCompactInduction G π ⟶ D :=
  Classical.choose (exists_surjective_rationalNormKernelCompactInduction G π D h)

/-- The chosen map is surjective on the actual representation carriers. -/
theorem rationalNormKernelInertiaQuotient_surjective
    (D : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (h : IsRationalInertiaRelated G (rationalInertiaBaseLift G π) D) :
    Function.Surjective (SmoothRep.hom (rationalNormKernelInertiaQuotient G π D h)) :=
  Classical.choose_spec (exists_surjective_rationalNormKernelCompactInduction G π D h)

end Langlands.CuspidalSupport
