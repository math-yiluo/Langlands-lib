import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # Statement: pointed maps from connected group varieties to groups of multiplicative type -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Maps to groups of multiplicative type** (Milne, *Algebraic Groups* (2017),
Proposition 12.49). Let `G` be a connected group variety (a smooth connected group scheme of
finite type) over a field `k`, and let `T` be a group of multiplicative type over `k`. Every
morphism of `k`-schemes `φ : G → T` sending the identity of `G` to the identity of `T` is a
homomorphism of algebraic groups. -/
def MultiplicativeTypePointedMapStatement : Prop :=
  ∀ (k : Type u) [Field k] (G T : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    IsMultiplicativeType T →
    ∀ φ : G.X ⟶ T.X, η[G.X] ≫ φ = η[T.X] →
      ∃ f : G ⟶ T, f.hom.hom = φ

end Langlands.GroupScheme
