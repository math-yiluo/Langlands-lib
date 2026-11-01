import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Euler coefficients of actual section cokernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

local instance (X : Scheme.{u}) : (structureModule X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) :
    (tensorPow L.obj n).IsQuasicoherent :=
  (tensorPow_isLocallyFreeRankOne X L n).isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) (s : L.powSections n) :
    (cokernel (sectionHom (tensorPow L.obj n) s)).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_cokernel (sectionHom (tensorPow L.obj n) s)

/-- The Euler coefficient of a generically generating power section's actual
cokernel is the corresponding positive-step difference coefficient. -/
def SectionCokernelEulerCoefficientStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (d : ℕ), topologicalKrullDim X ≤ d + 1 →
    ∀ (L : LineBundle X) (n : ℕ) (s : L.powSections n),
      (L.sectionOpen s : Set X).Nonempty →
      ∀ (hQ : HasFiniteAffineSections (cokernel (sectionHom (tensorPow L.obj n) s))),
        HasSupportDimensionLT (cokernel (sectionHom (tensorPow L.obj n) s)) (d + 1) →
        (coherentEulerPolynomial f (cokernel (sectionHom (tensorPow L.obj n) s))
          hQ L d).coeff d =
          ((d + 1 : ℕ) : ℚ) * (n : ℚ) *
            (lineBundleEulerPolynomial f L (d + 1)).coeff (d + 1)

end Langlands.AlgebraicGeometry.Picard
