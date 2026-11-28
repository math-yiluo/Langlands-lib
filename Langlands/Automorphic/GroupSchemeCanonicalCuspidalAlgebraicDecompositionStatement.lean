import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Algebraic decomposition of classical cusp forms in the canonical Hilbert space -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

universe u

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme AdelicGroupPoints

/-- An invariant Hilbert sum of the full cuspidal space restricts to an internal algebraic
direct sum of its intersections with the square-integrable classical cuspidal image. -/
def GroupSchemeCanonicalCuspidalAlgebraicDecompositionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    let S := canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG
    letI : CompleteSpace S :=
      (isClosed_canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG).completeSpace_coe
    let C := (canonicalCuspidalFormL2Image F G centralSplitTorusCharacter
      (K.comap (ofInfinite F G).toMonoidHom) rho hsmooth hcalc hPD hG hrho
      hK.isMaximalCompact_comap_ofInfinite hN).toSubmodule.comap S.subtype
    let π := (canonicalFullAEL2CuspidalSubrepresentation F G
      centralSplitTorusCharacter hPD hG).toRepresentation
    ∀ (Index : Type u) [DecidableEq Index] (P : Index → Submodule ℂ S)
      [∀ i, CompleteSpace (P i)],
      IsHilbertSum ℂ (fun i => ↥(P i)) (fun i => (P i).subtypeₗᵢ) →
      (∀ i (g : AdelicGroupPoints F G) v, v ∈ P i → π g v ∈ P i) →
      (∀ i v, v ∈ C → (P i).starProjection v ∈ C) ∧
      (∀ v ∈ C, ∃ s : Finset Index, ∑ i ∈ s, (P i).starProjection v = v) ∧
      DirectSum.IsInternal (fun i => (P i).comap C.subtype)

end Langlands.Global.RestrictionSplitCentre
