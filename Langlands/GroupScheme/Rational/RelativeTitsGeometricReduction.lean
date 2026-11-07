import Langlands.GroupScheme.Rational.RelativeTitsCoreAssembly
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction

/-! # The relative Tits system from two geometric statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The rational Bruhat and actual rank-one statements suffice for the
relative Tits system. Both geometric inputs remain explicit premises. -/
def RelativeTitsGeometricPremises : Prop :=
  RationalBruhatStatement.{u} ∧ RootRankOneFactorizationStatement.{u}

/-- Rank-one factorization supplies the root-system, reflection, Coxeter
and ordered-product inputs of the published Tits assembly. -/
theorem relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization
    (hBr : RationalBruhatStatement.{u})
    (hRank : RootRankOneFactorizationStatement.{u}) :
    RelativeTitsSystemStatement.{u} := by
  have hroot := relativeRootSystemStatement_of_rootRankOneFactorizationStatement hRank
  have hstruct : RootGeneratedCentralizerStructuralPremises.{u} := ⟨hroot, hRank⟩
  exact relativeTitsSystemStatement_of_coreStatements
    hstruct.relativeWeylCoxeter standardParabolicEndpoints hBr hRank hroot
    genericCentralizer hstruct.dynamicRootOrderedProduct

/-- The bundled form of the two-input reduction. -/
theorem RelativeTitsGeometricPremises.relativeTitsSystemStatement
    (h : RelativeTitsGeometricPremises.{u}) : RelativeTitsSystemStatement.{u} :=
  relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization h.1 h.2

/-- Rational Bruhat and reductivity of the actual full-kernel centralizer
components give opposite pairs, hence the full rank-one and Tits conclusions.
The two unproved geometric statements remain explicit premises. -/
theorem relativeTitsSystemStatement_of_bruhat_and_kernelCentralizerComponentReductivity
    (hBr : RationalBruhatStatement.{u})
    (hRed : RelativeRoot.KernelCentralizerComponentReductiveStatement.{u}) :
    RelativeTitsSystemStatement.{u} := by
  apply relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization hBr
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  apply RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs i hi.isSplitSubtorus.1
  intro a ha x hx _hx1
  exact RelativeRoot.exists_oppositeFactorPair_of_bruhat_and_componentReductivity
    hBr hRed k G hG T i hi a ha.1 x hx

end Langlands.GroupScheme
