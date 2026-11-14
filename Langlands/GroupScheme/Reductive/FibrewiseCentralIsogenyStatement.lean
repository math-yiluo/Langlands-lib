import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: central isogenies of reductive group schemes are detected on fibres -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Central isogenies are detected on fibres** (Conrad, *Reductive group schemes* (2014),
Proposition 3.3.10, with central isogenies as in Definition 3.3.9). Let `f : G' ⟶ G` be a
homomorphism of reductive group schemes over a scheme `S` whose underlying morphism of
schemes is surjective. Then `f` is a central isogeny if and only if, for every point `s ∈ S`,
the fibre `f_s : G'_s ⟶ G_s` over the residue field `κ(s)` has finite central kernel: the
scheme-theoretic kernel of `f_s` is finite over `κ(s)` and central in `G'_s`. -/
def ReductiveFibrewiseCentralIsogenyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G' G : GroupScheme S), IsReductive G' → IsReductive G →
    ∀ f : G' ⟶ G, Surjective f.hom.hom.left →
      (IsCentralIsogeny f ↔
        ∀ s : S,
          let f_s := (GroupScheme.baseChange (S.fromSpecResidueField s)).map f
          IsFinite (kernel f_s).X.hom ∧ IsCentral (kernelι f_s))

end Langlands.GroupScheme
