import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Fixed-profile cuspidal finiteness on the canonical adelic quotient -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
open AdelicGroupPoints InfiniteAdelicGroupPoints

/-- Cuspidal classes with automorphic representatives of the specified finite level,
central ideal and compact profiles form a finite-dimensional submodule of `L²([G])`. -/
def GroupSchemeCanonicalFixedProfileCuspidalFinitenessStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (L : Subgroup (FiniteAdelicGroupPoints F G)), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
    ∀ (E : Submodule ℂ (K.comap (ofInfinite F G).toMonoidHom → ℂ)), FiniteDimensional ℂ E →
    ∃ W : Submodule ℂ (Lp ℂ 2 (canonicalMeasure F G)), FiniteDimensional ℂ W ∧
      ∀ v : Lp ℂ 2 (canonicalMeasure F G), v ∈ W ↔
        v ∈ canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG ∧
        ∃ φ : AdelicGroupPoints F G → ℂ,
          IsAutomorphicFunctionOn F G hsmooth hcalc (AdelicGroupPoints.rationalSubgroup F G)
            (K.comap (ofInfinite F G).toMonoidHom) rho φ ∧
          IsLeftInvariantUnder F G (canonicalSubgroup F G) φ ∧
          (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, φ (g * ofFinite F G b) = φ g) ∧
          (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
            ∀ h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G,
              plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G φ b, h⟩ = 0) ∧
          (∀ g : AdelicGroupPoints F G,
            (fun k : K.comap (ofInfinite F G).toMonoidHom => φ (g * ofInfinite F G k)) ∈ E) ∧
          (v : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G] (fun y => φ y.out)

end Langlands.Global.RestrictionSplitCentre
