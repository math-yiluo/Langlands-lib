import Langlands.AbelianScheme.Isogeny
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: fibrewise isogenies of reductive group schemes are isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fibrewise isogenies are isogenies** (Conrad, *Reductive group schemes* (2014),
Proposition 6.1.10, with isogenies as in Definition 3.3.9). Let `f : G' ⟶ G` be a homomorphism
of reductive group schemes over a scheme `S`. If for every point `s ∈ S` the fibre
`f_s : G'_s ⟶ G_s` over the residue field `κ(s)` is an isogeny (a finite flat surjection),
then `f` is an isogeny. -/
def ReductiveFibrewiseIsogenyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G' G : GroupScheme S), IsReductive G' → IsReductive G →
    ∀ f : G' ⟶ G,
      (∀ s : S, IsIsogeny ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f)) →
        IsIsogeny f

end Langlands.GroupScheme
