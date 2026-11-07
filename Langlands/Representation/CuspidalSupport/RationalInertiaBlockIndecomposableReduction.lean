import Langlands.Representation.CuspidalSupport.RationalInertiaBlockIndecomposableStatement
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelEndDomainProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelSummand
import Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent

/-!
# Renard VI.4.5, Corollary, from VI.4.1 and the first clause of VI.3.2(i)

The indecomposability of the inertia block `M(G)[π]` follows from the VI.4.1
equivalence `Hom(Π, •)` for `Π = ind ρ`, the domain property of `End Π` (VI.4.3,
proved in the Library) and the existence of an irreducible summand `ρ` of the
restriction of `π` to the common norm kernel (first clause of VI.3.2(i)). Neither
VI.4.1 nor VI.3.2(i) is proved in the Library at the time of writing, so this module
proves the target only under these two published statements as hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The implication proved in this module: the VI.4.1 Theorem and VI.3.2(i) imply the
Corollary of VI.4.5, at the same field and carrier universes. -/
def RationalInertiaBlockIndecomposableReductionClause : Prop :=
  RationalSummandHomEquivalenceStatement.{uF, uV} →
    RationalNormKernelOrbitStatement.{uF, uV} →
      RationalInertiaBlockIndecomposableStatement.{uF, uV}

/-- Renard VI.4.5, Corollary, from the VI.4.1 Theorem
`RationalSummandHomEquivalenceStatement` and VI.3.2(i)
`RationalNormKernelOrbitStatement` (only its first clause, the existence of an
irreducible subrepresentation of the restriction to the common norm kernel, is used).
The domain property of VI.4.3 is the published `rationalNormKernelEnd_isDomain`. -/
theorem rationalInertiaBlockIndecomposable_of_homEquivalence
    (hEq : RationalSummandHomEquivalenceStatement.{uF, uV})
    (hOrbit : RationalNormKernelOrbitStatement.{uF, uV}) :
    RationalInertiaBlockIndecomposableStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp P hP
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  obtain ⟨W, hW⟩ := (hOrbit F G hG π hπ).1
  let H := rationalCommonNormKernel G
  let ρ := restrictionSummand H π W
  have hρ : ρ.IsIrreducible := restrictionSummand_isIrreducible H π W hW
  obtain ⟨hmem, hEqv⟩ := hEq F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ
    (restrictionSummandι H π W) (restrictionSummandι_injective H π W)
  have : IsDomain (End ((Induction.compactInductionFunctor H).obj
      (SmoothRep.toRep.obj ρ))) :=
    rationalNormKernelEnd_isDomain F G hG ρ hρ
  exact Renard.exists_isZero_of_decomposition_fullSubcategory
    (⟨_, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π)) hP

theorem rationalInertiaBlockIndecomposableReductionClause_holds :
    RationalInertiaBlockIndecomposableReductionClause.{uF, uV} :=
  rationalInertiaBlockIndecomposable_of_homEquivalence

end Langlands.CuspidalSupport
