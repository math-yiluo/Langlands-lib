import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: local finite free representations with central kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Local matrix representations with central kernel** (SGA 3, Exposé XI,
Corollary 6.11(b) applied to `H = G`, and Exposé XVI, Proposition 3.1 and the
first lines of its proof).

Let `G` be a smooth, separated, quasi-compact group scheme over an
arbitrary scheme `S` whose residue-field fibres are connected. Every point of
`S` lies in an affine open `Spec R ⟶ S` over which `G` has a finite free matrix
representation `ρ` whose kernel is central: a point of `G` over any test scheme
which `ρ` sends to the identity commutes with every point of `G` over that test
scheme. -/
def LocalCentralKernelRepresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) →
    ∀ s : S, ∃ (R : CommRingCat.{u}) (i : Spec R ⟶ S),
      IsOpenImmersion i ∧ s ∈ Set.range i.base ∧
      ∃ (m : ℕ) (ρ : MatrixRepresentation ((GroupScheme.baseChange i).obj G) (Fin m)),
        ∀ (U : Over (Spec R)) (g h : U ⟶ ((GroupScheme.baseChange i).obj G).X),
          g ≫ ρ.hom.hom = 1 → g * h = h * g

end Langlands.GroupScheme
