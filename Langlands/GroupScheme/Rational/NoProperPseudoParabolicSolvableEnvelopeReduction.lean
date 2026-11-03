import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeStatement
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralStatement
import Langlands.GroupScheme.Rational.UnipotentQuotientSplitTorusPreimageStatement
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientStatement

/-! # Reduction of the solvable envelope to radical, quotient and preimage statements

The solvable envelope is the preimage of the largest central split torus of the
quotient by the ground-field unipotent radical.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Radical existence, the pseudo-reductive quotient, centrality of split tori in
that quotient and the preimage construction imply the solvable envelope. -/
def NoProperPseudoParabolicSolvableEnvelopeReductionStatement : Prop :=
  UnipotentRadicalExistenceStatement.{u} →
    UnipotentRadicalQuotientStatement.{u} →
      NoProperPseudoParabolicSplitTorusCentralStatement.{u} →
        UnipotentQuotientSplitTorusPreimageStatement.{u} →
          NoProperPseudoParabolicSolvableEnvelopeStatement.{u}

/-- Radical existence, the pseudo-reductive quotient, centrality of split tori in
that quotient and the preimage construction imply the solvable envelope. -/
theorem noProperPseudoParabolicSolvableEnvelope_of_statements
    (hrad : UnipotentRadicalExistenceStatement.{u})
    (hquot : UnipotentRadicalQuotientStatement.{u})
    (hcent : NoProperPseudoParabolicSplitTorusCentralStatement.{u})
    (hpre : UnipotentQuotientSplitTorusPreimageStatement.{u}) :
    NoProperPseudoParabolicSolvableEnvelopeStatement.{u} := by
  intro k _ G _ _ _ hno
  obtain ⟨U, r, hr⟩ := hrad k G
  obtain ⟨Q, q, hq, hQ⟩ := hquot k G U r hr
  have : Smooth Q.X.hom := hQ.smooth
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  obtain ⟨B, z, hz, huniv⟩ :=
    exists_largestCentralSplitTorus Q (finiteType_coordinateAlgebra Q)
  obtain ⟨H, j, hj, hHs, hHc, hHa, hHsol, hfac⟩ :=
    hpre k G U r hr.isClosedSubgroup hr.smooth hr.connectedSpace hr.isUnipotent Q q hq B z hz.1
  refine ⟨H, j, hj, hHs, hHc, hHa, hHsol, fun S i hi => ?_⟩
  obtain ⟨g, hg⟩ := huniv S (i ≫ q) hi.1 (hcent k G hno U r hr Q q hq hQ S i hi)
  exact hfac S.toGrp i g hg

/-- The conditional reduction, as a proposition with its proof. -/
theorem noProperPseudoParabolicSolvableEnvelopeReduction :
    NoProperPseudoParabolicSolvableEnvelopeReductionStatement.{u} :=
  noProperPseudoParabolicSolvableEnvelope_of_statements

end Langlands.GroupScheme
