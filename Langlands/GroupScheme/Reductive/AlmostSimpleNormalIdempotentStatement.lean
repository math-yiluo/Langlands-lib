import Langlands.GroupScheme.Reductive.AlmostSimple

/-! # Statement: normal idempotents of an almost-simple field group -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A conjugation-equivariant idempotent endomorphism of an almost-simple
field group is trivial or the identity. The trivial group homomorphism is `0`. -/
def AlmostSimpleNormalIdempotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAlmostSimple G → ∀ (ψ : G ⟶ G), ψ ≫ ψ = ψ →
      (∀ (T : Over (Spec (CommRingCat.of k))) (h x : T ⟶ G.X),
        (h * x * h⁻¹) ≫ ψ.hom.hom = h * (x ≫ ψ.hom.hom) * h⁻¹) →
      ψ = 0 ∨ ψ = 𝟙 G

end Langlands.GroupScheme
