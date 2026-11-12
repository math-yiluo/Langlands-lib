import Langlands.GroupScheme.Adjoint.ExistenceStatement
import Langlands.GroupScheme.Adjoint.Assembly
import Langlands.GroupScheme.Adjoint.CenterQuotientReductiveProof
import Langlands.GroupScheme.Adjoint.CenterQuotientDescent
import Langlands.GroupScheme.Adjoint.SecondCenterReductive
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.NormalQuotientExistenceProof

/-! # Existence of the actual adjoint quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of the actual adjoint quotient.** Every connected reductive group over an
arbitrary field has an actual adjoint quotient by its full scheme-theoretic centre. -/
theorem adjointQuotientExistence : AdjointQuotientExistenceStatement.{u} := by
  intro k _ G hG
  have : Smooth G.X.hom := hG.smooth
  -- A closed representative of the full centre, which is a normal subgroup.
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  -- The affine fppf quotient by that representative.
  obtain ⟨Q, q, hQa, hQf, hq⟩ :=
    normalSubgroupQuotientExistence k G Z z hG.isAffineHom inferInstance hz.1 hz.isNormal
  rw [hz.2] at hq
  have hQ : IsConnectedReductive Q := centerQuotientReductive k G Q q hG hQa hQf hq
  have hc : center Q = ⊥ :=
    CenterQuotientCenter.center_eq_bot_of_secondCenterTrivial q hq
      (SecondCenter.secondCenterTrivial_of_centralDerivedProduct
        reductiveCentralDerivedProduct k G hG)
  obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
  exact ⟨Q, q, isAdjointQuotient_of_fppf_kernel_range q hG hQ hc hflat hsurj hlfp hker⟩

end Langlands.GroupScheme
