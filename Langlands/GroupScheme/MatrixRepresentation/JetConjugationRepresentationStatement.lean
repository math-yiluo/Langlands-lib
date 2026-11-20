import Langlands.GroupScheme.IdentityJetCentralizer
import Langlands.GroupScheme.MatrixRepresentation

/-! # Statement: conjugation on an identity jet as a local matrix representation -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The conjugation representation on an identity jet** (SGA 3, Exposé XVI,
Proposition 3.1, the representation `ρ_n`, with its kernel the centralizer of
the `n`-th infinitesimal neighbourhood of the unit section).

Let `G` be a smooth, separated group scheme over an arbitrary scheme `S`, and
let `n` be a natural number. Every point `s` of `S` has arbitrarily small affine
open neighbourhoods `Spec R ⟶ S` over which `G` has a finite free matrix
representation `ρ` whose kernel is exactly the centralizer of the order-`n`
identity jet: a point `g` on any test scheme satisfies `g ≫ ρ = 1` if and only
if it centralizes the jet. -/
def JetConjugationRepresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom →
    ∀ (n : ℕ) (s : S) (W : S.Opens), s ∈ W →
      ∃ (R : CommRingCat.{u}) (i : Spec R ⟶ S),
        IsOpenImmersion i ∧ s ∈ Set.range i.base ∧ Set.range i.base ⊆ W ∧
        ∃ (m : ℕ) (ρ : MatrixRepresentation ((GroupScheme.baseChange i).obj G) (Fin m)),
          ∀ (U : Over (Spec R)) (g : U ⟶ ((GroupScheme.baseChange i).obj G).X),
            g ≫ ρ.hom.hom = 1 ↔ IdentityJet.CentralizesJet ((GroupScheme.baseChange i).obj G) n g

end Langlands.GroupScheme
