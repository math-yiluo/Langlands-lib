import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: rigidity of families of homomorphisms between diagonalizable groups -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Rigidity of diagonalizable groups** (Milne, *Algebraic Groups* (2017), Theorem 12.36).
Let `k` be a field, let `G` and `H` be diagonalizable algebraic groups over `k` (isomorphic to
`D(Λ)` and `D(Λ')` for finitely generated abelian groups `Λ` and `Λ'`), and let `X` be a
connected algebraic scheme over `k`. Let `φ : X × G → H` be a morphism such that for every
point `x` of `X` the map `g ↦ φ(x, g)` is a homomorphism on points. Then for every
`k`-point `x₀` of `X`, `φ(x, g) = φ(x₀, g)` for all points `(x, g)` of `X × G`. -/
def DiagonalizableRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ'], AddGroup.FG Λ → AddGroup.FG Λ' →
    Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) →
    Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp) →
    ∀ (X : Over (Spec (CommRingCat.of k))), LocallyOfFiniteType X.hom → QuasiCompact X.hom →
      ConnectedSpace X.left →
      ∀ φ : X ⊗ G.X ⟶ H.X,
        (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g g' : T ⟶ G.X),
          lift x (g * g') ≫ φ = (lift x g ≫ φ) * (lift x g' ≫ φ)) →
        ∀ (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
          (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g : T ⟶ G.X),
          lift x g ≫ φ = lift (toUnit T ≫ x₀) g ≫ φ

end Langlands.GroupScheme
