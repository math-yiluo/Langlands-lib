import Langlands.GroupScheme.Lie.RootOrbitCharacterAction
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Split

/-!
# Statement: Galois descent of torus points with prescribed character values

Let `L / k` be a Galois extension and `T` a commutative group scheme over `k` whose base
change `T_L` is a split torus. Every Galois-equivariant homomorphism
`φ : X^*(T_L) → Lˣ` is the evaluation of the characters at some `k`-point of `T`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Galois descent of torus points with prescribed character values.** For a field `k`,
a Galois extension `L / k` (not necessarily finite) and a commutative group scheme `T` over
`k` whose base change `T_L` is a split torus, every homomorphism `φ : X^*(T_L) → Lˣ`
(written additively as `X^*(T_L) →+ Additive Lˣ`) that is equivariant for the Galois
action on characters, `φ (σ χ) = σ (φ χ)` for all `σ ∈ Aut_k(L)` and `χ ∈ X^*(T_L)`, is the
evaluation of characters at a `k`-point `h` of `T`: `χ (h_L) = φ χ` for every `χ`, where
`h_L` is `h` viewed as an `L`-point of `T_L`. -/
def TorusEquivariantCharacterValueDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [IsGalois k L]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp) →
    ∀ φ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T) →+
        Additive Lˣ,
      (∀ (σ : L ≃ₐ[k] L)
          (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)),
        (((φ (characterLattice.galoisRepresentation k L T σ χ)).toMul : Lˣ) : L) =
          σ (((φ χ).toMul : Lˣ) : L)) →
      ∃ h : Lie.AffinePoints T.toGrp k,
        ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T),
          Lie.characterValue χ (rationalBaseChangePoint k L T h) = (φ χ).toMul

end Langlands.GroupScheme
