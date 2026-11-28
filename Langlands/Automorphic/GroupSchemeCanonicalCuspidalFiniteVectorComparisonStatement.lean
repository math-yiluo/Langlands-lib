import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.Global.AdelicL2FiniteVectorDensity
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Representation.Unitary.DiscretePart

/-! # Finite vectors in finite orthogonal sums of canonical cuspidal representations -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

universe u

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme AdelicGroupPoints

/-- On a finite orthogonal sum of irreducible subspaces of the canonical cuspidal
space, the classical cuspidal classes are precisely the compact-finite, finite-level vectors. -/
def GroupSchemeCanonicalCuspidalFiniteVectorComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    ∀ (Index : Type u) [Fintype Index] (V : Index → Submodule ℂ (Lp ℂ 2 (canonicalMeasure F G))),
      (∀ i, Langlands.Analysis.IsIrreducibleSubrepresentation
        (canonicalL2RightAction F G centralSplitTorusCharacter hG) (V i)) →
      (∀ i, V i ≤ canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG) →
      OrthogonalFamily ℂ (fun i => ↥(V i)) (fun i => (V i).subtypeₗᵢ) →
      ∀ w ∈ ⨆ i, V i,
        w ∈ canonicalCuspidalFormL2Image F G centralSplitTorusCharacter
          (K.comap (ofInfinite F G).toMonoidHom) rho hsmooth hcalc hPD hG hrho
          hK.isMaximalCompact_comap_ofInfinite hN ↔
        IsCanonicalL2FiniteVector hG K w

end Langlands.Global.RestrictionSplitCentre
