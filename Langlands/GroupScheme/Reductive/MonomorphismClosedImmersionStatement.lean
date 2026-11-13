import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Statement: monomorphisms out of reductive group schemes are closed immersions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Monomorphisms out of reductive group schemes are closed immersions** (Conrad, *Reductive
group schemes* (2014), Theorem 5.3.5, first sentence). Let `G` be a reductive group scheme over
an arbitrary scheme `S`, and let `G'` be a separated `S`-group scheme of finite presentation
(locally of finite presentation and quasi-compact; quasi-separatedness follows from
separatedness). Every homomorphism `f : G ⟶ G'` whose underlying morphism of schemes is a
monomorphism is a closed immersion. -/
def ReductiveMonomorphismClosedImmersionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G G' : GroupScheme S), IsReductive G →
    IsSeparated G'.X.hom → LocallyOfFinitePresentation G'.X.hom → QuasiCompact G'.X.hom →
    ∀ f : G ⟶ G', Mono f.hom.hom.left → IsClosedImmersion f.hom.hom.left

end Langlands.GroupScheme
