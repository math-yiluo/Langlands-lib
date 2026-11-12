import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat

/-! # Characters and homomorphisms of diagonalizable groups: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Characters and homomorphisms of diagonalizable groups** (Milne, *Algebraic Groups*
(2017), Lemma 12.4 with the sentence after it, and Theorem 12.9(a)). Let `k` be a field and
let `Λ`, `Λ'` be finitely generated abelian groups.

1. For every `m ∈ Λ` there is a character of `D(Λ)` whose value at a point `t` (a character
   `Λ → Γ(U)ˣ`) is `t(m)`, and every character of `D(Λ)` has this form for exactly one `m`.
   So `X(D(Λ)) ≅ Λ`.
2. Every homomorphism `D(Λ) ⟶ D(Λ')` is `Diagonalizable.restrictMap g` for exactly one
   additive map `g : Λ' →+ Λ`: the functor `Λ ↦ D(Λ)` is fully faithful. -/
def DiagonalizableCharacterStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
      (∀ m : Λ, ∃ χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ),
        ∀ (U : Over (Spec (CommRingCat.of k)))
          (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
          Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ).hom.hom) =
            Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ U x
              (Multiplicative.ofAdd m)) ∧
      (∀ χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ),
        ∃! m : Λ, ∀ (U : Over (Spec (CommRingCat.of k)))
          (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
          Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ).hom.hom) =
            Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ U x
              (Multiplicative.ofAdd m))) ∧
    (∀ (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ'] [AddGroup.FG Λ] [AddGroup.FG Λ'],
      Function.Bijective
        (fun g : Λ' →+ Λ => Diagonalizable.restrictMap (CommRingCat.of k) g))

end Langlands.GroupScheme
