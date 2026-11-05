import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateAlgebra

/-! # Local hypersurface divisibility for actual unramified regular scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

/-- An irreducible actual regular scalar with a zero in an open character
region divides every actual regular scalar vanishing on its zeros there. -/
def RationalUnramifiedLocalHypersurfaceDivisibilityStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [TopologicalSpace (GroupScheme.rationalPoints G)],
    Continuous (rationalValuationImageProjection G) →
    GroupScheme.IsConnectedReductive G →
    ∀ (U : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)))
      (p a : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)),
      IsOpen U → Irreducible p →
      (∃ χ ∈ U, p.val χ = 0) →
      (∀ χ ∈ U, p.val χ = 0 → a.val χ = 0) →
      p ∣ a

end Langlands.Plancherel
