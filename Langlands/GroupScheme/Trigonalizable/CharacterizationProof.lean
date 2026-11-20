import Langlands.GroupScheme.Trigonalizable.CharacterizationStatement
import Langlands.GroupScheme.Trigonalizable.Flag
import Langlands.GroupScheme.Trigonalizable.TriangularEmbedding
import Langlands.GroupScheme.Trigonalizable.UnipotentQuotient

/-! # Characterizations of trigonalizable groups (Milne 16.2): proof

The first equivalence is `Trigonalizable.isTrigonalizable_iff_exists_stableFlag`. The other two
follow from the cycle of implications (a) ⇒ (c) ⇒ (d) ⇒ (a).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.2: the characterizations of trigonalizable affine algebraic
groups over a field. -/
theorem trigonalizableCharacterization : TrigonalizableCharacterizationStatement.{u} := by
  intro k _ G _ _
  have hac := Trigonalizable.exists_closed_triangular_of_isTrigonalizable (G := G)
  have hcd : (∃ (N : ℕ) (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N)
      (CommRingCat.of k) (fun i => -(i.val : ℤ))), IsClosedSubgroup j) →
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
        (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
        (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
        IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q :=
    fun ⟨_, j, hj⟩ =>
      Trigonalizable.exists_unipotent_diagonalizable_quotient_of_closed_triangular j hj
  have hda : (∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
      (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
      (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) → IsTrigonalizable G :=
    fun ⟨_, i, _, _, _, q, hi, hU, hN, hq⟩ =>
      Trigonalizable.isTrigonalizable_of_unipotent_diagonalizable_quotient i q hi hU hN hq
  exact ⟨Trigonalizable.isTrigonalizable_iff_exists_stableFlag,
    ⟨hac, fun h => hda (hcd h)⟩, ⟨fun h => hcd (hac h), hda⟩⟩

end Langlands.GroupScheme
