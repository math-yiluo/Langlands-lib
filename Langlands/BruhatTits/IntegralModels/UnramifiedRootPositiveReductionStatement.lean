import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Positive reduction in a single unramified root model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

private instance rootPositiveReduction_neutralSmooth
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

/-- **KP Lemma 8.4.4, with the integral-section preimage of Corollary 8.4.5.**
In a characterized unramified zero-fixer model, an actual integral root
section reduces into the unipotent radical exactly when its generic image
has positive root depth at some point of the bounded apartment subset.

The integral apartment torus and reductive quotient are supplied inputs.
The existential point quantifier is essential for a general bounded subset:
the positive subgroup here is the union in KP 8.4.3, intersected with the
zero-depth root fixer. -/
def UnramifiedRootPositiveReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (Ω : Set C.Apartment),
    Ω.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) →
    ∀ (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G),
      D.neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      ∀ (A : IntegralSplitTorusData D.neutral C.i)
        (Q : SpecialFibreQuotientData D),
        Q.IsReductiveQuotient →
        ∀ (a : relativeRoots C.i)
          (u : (A.rootModel a a.2.1).integralSections),
          D.neutral.reduction
              (rationalPoints.map (A.rootModelMap a a.2.1).hom u) ∈ Q.radicalPoints ↔
            ∃ x ∈ Ω,
              rationalPoints.map (A.rootInclusion a a.2.1)
                  ((A.rootModel a a.2.1).integralPointMap u) ∈
                C.apartment.filtrationPlus x a 0

end Langlands.BruhatTits.IntegralModels
