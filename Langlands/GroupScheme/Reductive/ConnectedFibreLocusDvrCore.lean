import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # The discrete-valuation-ring case of the connected-fibre specialization -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace ConnectedFibreLocus

/-- **Connectedness specializes over a discrete valuation ring.** Let `R` be a discrete
valuation ring with fraction field `K` and residue field `k`, and let `G` be a smooth affine
`R`-group whose geometric fibres have reductive identity components. If the generic fibre
`G_K` is connected, then the special fibre `G_k` is connected.

This is the local input of Conrad, *Reductive group schemes* (2014), Proposition 3.1.12,
used by the proof of `ConnectedFibreLocusClosedStatement` in this task. -/
def DvrCoreStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    identityComponentReductiveLocus G = Set.univ →
      ConnectedSpace ((baseChange (algebraBaseMap R K)).obj G).X.left →
        ConnectedSpace
          ((baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).obj G).X.left

end ConnectedFibreLocus

end Langlands.GroupScheme
