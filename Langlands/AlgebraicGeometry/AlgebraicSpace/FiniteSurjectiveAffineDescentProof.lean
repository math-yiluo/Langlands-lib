import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentTransferProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineRelationProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSerreCriterionProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodulesAcyclicProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianFirstLevelProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianCoverLevelProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianApproximationStatement
import Langlands.AlgebraicGeometry.NoetherianEtaleEquivalenceRelationAffineDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentStatement

/-! # Finite-surjective descent of affineness for algebraic spaces

Stacks Project Lemma 70.15.1 (Tag 07VS), assembled from the published theorems T, A, Key,
Serre, FL, NL and DS.
-/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The Noetherian case (Tag 07VP for presentations), from A, Key and Serre. -/
theorem noetherianEtaleEquivalenceRelationAffineDescent :
    NoetherianEtaleEquivalenceRelationAffineDescentStatement.{u} := by
  intro E hU hN hcov
  obtain ⟨hR, hj⟩ := etaleEquivalenceRelationAffineRelation E hU hcov
  exact etaleEquivalenceRelationSerreCriterion E hU hN hR hj
    (etaleEquivalenceRelationComodulesAcyclic E hU hN hR hj hcov)

/-- Absolute Noetherian approximation for presentations, from A, FL, NL and DS. -/
theorem etaleEquivalenceRelationNoetherianApproximation :
    EtaleEquivalenceRelationNoetherianApproximationStatement.{u} := by
  intro hN E hU hcov
  obtain ⟨-, hj⟩ := etaleEquivalenceRelationAffineRelation E hU hcov
  obtain ⟨E₀, f, g, hfg, hU₀, hN₀, hR₀⟩ := etaleEquivalenceRelationNoetherianFirstLevel E hU hj
  obtain ⟨E₁, f₁, g₁, hfg₁, hU₁, hN₁, hcov₁⟩ :=
    etaleEquivalenceRelationNoetherianCoverLevel E E₀ f g hfg hU hU₀ hN₀ hR₀ hcov
  exact etaleEquivalenceRelationCartesianAffineQuotient E E₁ f₁ g₁ hfg₁ hU hU₁
    (hN E₁ hU₁ hN₁ hcov₁)

/-- Stacks Project Lemma 70.15.1 (Tag 07VS): if `f : X ⟶ Y` is a finite surjective morphism of
algebraic spaces over `S` and `X` is affine, then `Y` is affine. -/
theorem finiteSurjectiveAffineDescent : FiniteSurjectiveAffineDescentStatement.{u} :=
  etaleEquivalenceRelationAffineDescentTransfer
    (etaleEquivalenceRelationNoetherianApproximation
      noetherianEtaleEquivalenceRelationAffineDescent)

end Langlands.AlgebraicGeometry.AlgebraicSpace
