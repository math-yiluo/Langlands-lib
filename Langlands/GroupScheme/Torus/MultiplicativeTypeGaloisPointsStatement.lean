import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.AffinePoints
import Mathlib.FieldTheory.IsSepClosed

/-! # Statement: points of a group of multiplicative type over subfields of `kˢ` (Milne 12.26) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Points of a group of multiplicative type** (Milne, *Algebraic Groups*, Remark 12.26).
Let `G` be an affine group scheme of finite type and of multiplicative type over a field `k`,
let `Ks` be a separable closure of `k`, and let `K` be an intermediate field of `Ks / k`.
Let `Γ = Aut_k(Ks)` act on the characters `X^*(G) = X(G_{Ks})` by
`rationalCharacters.galoisRepresentation`, and let `Γ_K` be the subgroup fixing `K`. Then
evaluation of characters, `x ↦ (χ ↦ χ(x))`, is a bijection from the `K`-points of `G` onto
the set of homomorphisms `f : X^*(G) → Ksˣ` satisfying `f (σ χ) = σ (f χ)` for all
`σ ∈ Γ_K` and all `χ`.

This is a statement only; nothing is proved here. -/
def MultiplicativeTypeGaloisPointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom], IsMultiplicativeType G →
    ∀ (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
      (K : IntermediateField k Ks),
      let value : G.affinePoints (CommAlgCat.of k K) →
          rationalCharacters (GaloisPointComparison.baseChanged k Ks G) → Ksˣ :=
        fun x χ => rationalCharacterEval χ
          ((GaloisPointComparison.baseChangeCoeffEquiv k Ks G).symm
            (G.affinePointMap (CommAlgCat.ofHom K.val) x))
      Function.Injective value ∧
        Set.range value =
          {f | (∀ χ ψ, f (χ + ψ) = f χ * f ψ) ∧
            ∀ σ : Ks ≃ₐ[k] Ks, (∀ a ∈ K, σ a = a) →
              ∀ χ, f (rationalCharacters.galoisRepresentation k Ks G σ χ) =
                Units.map σ.toMonoidHom (f χ)}

end Langlands.GroupScheme
