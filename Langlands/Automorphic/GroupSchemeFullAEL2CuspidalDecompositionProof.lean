import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalDecompositionStatement
import Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionProof

/-! # Discrete decomposition of the full cuspidal Hilbert space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

set_option maxHeartbeats 2000000 in
/-- Compactness of the cuspidal convolutions gives an internal Hilbert sum
of irreducible closed invariant subspaces with finite multiplicities. -/
theorem groupSchemeFullAEL2CuspidalDecomposition :
    GroupSchemeFullAEL2CuspidalDecompositionStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ S πc hcompact
  have hinner : ∀ a x y, inner ℂ (πc a x) (πc a y) = inner ℂ x y := fun a x y =>
    (fullAEL2CuspidalRightTranslate F G hPD hG T i hi I e hc a).inner_map_map x y
  have hcont : ∀ x, Continuous (fun a => πc a x) := fun x =>
    (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc x).continuous
  have hD := Langlands.Analysis.invariantSubspaceDiscreteDecomposition
    (Measure.haar : Measure (AdelicGroupPoints F G)) πc hinner hcont
  obtain ⟨A, hgood, hpair, hspan, hfin⟩ := hD (⊤ : Submodule ℂ S)
    isClosed_univ (fun _ _ _ => Submodule.mem_top) (fun f hf => by
      change IsCompactOperator ((fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc
        Measure.haar f hf).comp (⊤ : Submodule ℂ S).subtypeL)
      exact (hcompact f hf).comp_clm _)
  let _ (P : A) : CompleteSpace (P.val : Submodule ℂ S) :=
    (hgood P.val P.property).2.2.1.completeSpace_coe
  have hOrtho : OrthogonalFamily ℂ (fun P : A => ↥P.val) (fun P => P.val.subtypeₗᵢ) := by
    apply orthogonalFamily_iff_pairwise.mpr
    intro P Q hPQ
    exact hpair P.property Q.property (fun h => hPQ (Subtype.ext h))
  have hTotal : (⨆ P : A, P.val).topologicalClosure = ⊤ := by
    rwa [← sSup_eq_iSup']
  exact ⟨A, fun P hP => (hgood P hP).2,
    IsHilbertSum.mkInternal (fun P : A => P.val) hOrtho hTotal.ge, hfin⟩

end Langlands.Automorphic.GroupSchemeFunctions
