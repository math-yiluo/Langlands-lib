import Langlands.GroupScheme.OrthogonalMatrix.Subgroups

/-!
# Automorphisms of the split even special orthogonal group: statement

This unproved statement records that every automorphism of the split special orthogonal
group `SO_{2n}`, the identity component of the split orthogonal group `O_{2n}` of the
hyperbolic quadratic form, over an arbitrary field is conjugation by a similitude of the
form (`Aut(SO_{2n}) = PGO_{2n}`), in every characteristic and for every `n ≥ 2`.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

/-- Let `L` be a field and `n ≥ 2`. Every automorphism `α` of the identity component
`SO_{2n}` of the split orthogonal group `groupScheme (Fin n) L` (the orthogonal group of the
hyperbolic form `q(x) = ∑ a, x (inl a) * x (inr a)` with Gram matrix `Q = formMatrix`) is
conjugation by a similitude of `q`: there are an invertible matrix `g` over `L` and a unit
`μ` with `g Q gᵀ - μ Q` alternating, such that on every test scheme `T` over `Spec L` the
automorphism sends the point with orthogonal matrix `x` to the point with matrix `g x g⁻¹`,
the entries of `g` and `g⁻¹` being mapped to the global sections of `T`.

This is an unproved statement (`Aut(SO_{2n}) = PGO_{2n}`; Knus–Merkurjev–Rost–Tignol,
*The Book of Involutions*, (26.15) and §26.B). There is no characteristic hypothesis. -/
def SpecialOrthogonalAutomorphismStatement : Prop :=
  ∀ (L : Type u) [Field L] (n : ℕ), 2 ≤ n →
    ∀ α : identityComponent (groupScheme (Fin n) (CommRingCat.of L)) ≅
        identityComponent (groupScheme (Fin n) (CommRingCat.of L)),
      ∃ (g : GL (Fin n ⊕ Fin n) L) (μ : Lˣ),
        IsAlt ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) * formMatrix (Fin n) L *
            (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L)ᵀ -
              (μ : L) • formMatrix (Fin n) L) ∧
        ∀ (T : Over (Spec (CommRingCat.of L)))
          (x : T ⟶ (identityComponent (groupScheme (Fin n) (CommRingCat.of L))).X),
          (pointsEquiv (Fin n) (CommRingCat.of L) T
              (x ≫ α.hom.hom.hom ≫
                (identityComponentι (groupScheme (Fin n) (CommRingCat.of L))).hom.hom) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(T.left, ⊤)) =
            (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L).map (scalarMap T) *
              (pointsEquiv (Fin n) (CommRingCat.of L) T
                (x ≫ (identityComponentι (groupScheme (Fin n) (CommRingCat.of L))).hom.hom) :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(T.left, ⊤)) *
              (↑g⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L).map (scalarMap T)

end Langlands.GroupScheme.OrthogonalMatrix
