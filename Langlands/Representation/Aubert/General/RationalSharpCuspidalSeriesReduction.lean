import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.SharpCuspidalSeriesReduction
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance
import Langlands.Representation.Aubert.General.RationalSharpReductionStatements

/-! # Cuspidal-series retention by `E#` from support retention and irreducibility -/

noncomputable section

universe u v uI uG uW

open CategoryTheory

namespace Langlands.Aubert.General

section Transport

variable {ι : Type uI}
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- Transport of irreducible inside-Levi cuspidal representations along the
association, from transport of inside-Levi cuspidality alone: conjugation is
pullback along a topological group isomorphism, so it preserves irreducibility. -/
theorem associationCuspidalTransport_of_isLeviCuspidal
    (hconj : ∀ (I J : Finset ι) (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n → ∀ σ : SmoothRep.{0, uG, uW} ℂ (M I),
        IsLeviCuspidal P M U hclosed I (hM I) (hL I) σ →
          IsLeviCuspidal P M U hclosed J (hM J) (hL J) ((conjugationFunctor n hn).obj σ)) :
    AssociationCuspidalTransport.{uI, uG, uW} P M U hclosed hM hL IsAssociate :=
  fun I J n hn hIJ σ hσ hc =>
    ⟨(isIrreducible_comp_continuousMulEquiv_iff σ.representation
        (conjugationEquiv n hn)).mpr hσ, hconj I J n hn hIJ σ hc⟩

end Transport

end Langlands.Aubert.General

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Cuspidal-series retention from the two sibling consequences: support
retention on `Alg({I})` and irreducibility of `E#` on `𝔈(I)`. -/
theorem rationalSharpCuspidalSeries_of_supportRetention_of_irreducible
    (hSupp : RationalSharpSupportRetentionStatement.{u, v})
    (hIrr : RationalSharpIrreducibleStatement.{u, v}) :
    RationalSharpCuspidalSeriesStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _
  exact sharpCuspidalSeries_of_irreducible_supportRetention
    (hIrr k G hG T i hi ν hν hStandard hOrder hInter hRoots hU hM hUc)
    (hSupp k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc)
    (rootAssociation_one i ν hN hZ)
    (associationCuspidalTransport_of_isLeviCuspidal (fun _ _ _ hn hIJ σ hc =>
      isLeviCuspidal_conjugation i ν hG hi hν hStandard hInter hRoots hN hZ hU hM
        hn hIJ σ hc))

/-- The published reduction statement holds, by
`rationalSharpCuspidalSeries_of_supportRetention_of_irreducible`. -/
theorem rationalSharpCuspidalSeriesReduction :
    RationalSharpCuspidalSeriesReductionStatement.{u, v} :=
  fun hSupp hIrr => rationalSharpCuspidalSeries_of_supportRetention_of_irreducible hSupp hIrr

end Langlands.Aubert.General.RationalPointFamily
