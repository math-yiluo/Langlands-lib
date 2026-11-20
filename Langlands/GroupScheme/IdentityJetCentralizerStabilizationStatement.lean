import Langlands.GroupScheme.IdentityJetCentralizer
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: the centralizer of a large identity jet is the centre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The centre is the centralizer of a large infinitesimal neighbourhood**
(SGA 3, Exposé XI, Corollary 6.11(b) with `H = G`, over an affine base).

Let `G` be a smooth, separated, quasi-compact group scheme over an affine
scheme `Spec R`, with connected residue-field fibres. Then there is `n` such
that every point of `G` which centralizes the order-`n` identity jet (after
every refinement of its test scheme) commutes with every point of `G` on the
same test scheme. -/
def JetCentralizerStabilizationStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R)),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : Spec R, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) →
    ∃ n : ℕ, ∀ (U : Over (Spec R)) (g : U ⟶ G.X), IdentityJet.CentralizesJet G n g →
      ∀ h : U ⟶ G.X, g * h = h * g

end Langlands.GroupScheme
