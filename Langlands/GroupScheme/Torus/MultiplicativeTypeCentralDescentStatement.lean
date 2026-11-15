import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.Characters
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Statement: descent of central homomorphisms from groups of multiplicative type -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Corollaire 5.4, for the two kinds of base change named there: a
faithfully flat quasi-compact morphism, or a morphism with a section. Let `H` be an `S`-group of
multiplicative type and of finite type, let `G` be a separated `S`-group of finite presentation,
and let `π : S' ⟶ S` be faithfully flat and quasi-compact or admit a section, with geometrically
connected fibres. Then every central homomorphism `u' : H_{S'} ⟶ G_{S'}` is the base change of
exactly one homomorphism `u : H ⟶ G`. -/
def MultiplicativeTypeCentralDescentStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (π : S' ⟶ S) (H G : GroupScheme S), IsMultiplicativeType H →
    IsSeparated G.X.hom → LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom →
    ((Flat π ∧ QuasiCompact π ∧ Surjective π) ∨ ∃ g : S ⟶ S', g ≫ π = 𝟙 S) →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ S),
      ConnectedSpace ↥(pullback π x)) →
    ∀ u' : (GroupScheme.baseChange π).obj H ⟶ (GroupScheme.baseChange π).obj G,
      IsCentral u' → ∃! u : H ⟶ G, (GroupScheme.baseChange π).map u = u'

end Langlands.GroupScheme
