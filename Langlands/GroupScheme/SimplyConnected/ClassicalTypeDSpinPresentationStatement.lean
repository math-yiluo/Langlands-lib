import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.GroupSchemes

/-!
# Spin presentations aligned with classical type-D indices

This unproved prerequisite states the classical type-D classification over an
arbitrary field, together with the index comparisons needed to read the division
degree and Witt index from an actual numbered Tits index.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A simply connected absolutely almost-simple group with a numbered type-D
diagram whose full star action fixes the nonfork vertices has an actual spin
presentation over a central division algebra. The presentation is chosen for
this numbering: its nonfork distinguished vertices are the positive multiples
of the division degree up to the Witt index, which equals the split rank.

This is an unproved general classification and index-comparison prerequisite.
There is no rank-one, local-field or characteristic hypothesis. -/
def ClassicalTypeDSpinPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n →
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a) →
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D)
      (degree m : ℕ),
      0 < degree ∧ Module.finrank K D = degree ^ 2 ∧ m * degree = 2 * n ∧
        ∃ σ : Quaternionic.FirstKindInvolution K D,
          Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
            ∃ q : σ.QuadraticForms (Fin m),
              σ.IsNondegenerateQuadratic q ∧
                σ.quadraticWittIndex q = splitRank G ∧
                (∀ a : d.Vertex, (e a).val + 2 < n →
                  (a ∈ d.distinguishedVertices ↔
                    ∃ j : ℕ, 0 < j ∧ j ≤ σ.quadraticWittIndex q ∧
                      (e a).val + 1 = j * degree)) ∧
                ∃ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π

end Langlands.GroupScheme
