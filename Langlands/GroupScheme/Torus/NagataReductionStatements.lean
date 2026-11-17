import Langlands.GroupScheme.Torus.NagataLinearlyReductiveStatement

/-! # The three independent implications in Nagata's theorem -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Linear reductivity is the exact all-test finite-coordinate semisimplicity
condition in the published Nagata statement. -/
def IsLinearlyReductive {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
    sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤

/-- The structural necessity part of Nagata's theorem: a linearly reductive
finite-type affine group in nonzero characteristic has multiplicative-type
identity component, including when the group is not smooth. -/
def NagataIdentityComponentNecessityStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsLinearlyReductive G →
        ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
          IsOpenImmersion i.hom.hom.left ∧
          Set.range i.hom.hom.left = IdentityComponent.identitySet G ∧
          IsMultiplicativeType H

/-- The finite-component necessity part of Nagata's theorem. -/
def NagataComponentOrderNecessityStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      IsLinearlyReductive G →
        ¬ p ∣ Nat.card (IdentityComponent.GeometricComponents k G)

/-- The sufficiency part of Nagata's theorem: multiplicative-type identity
component and prime-to-characteristic component order imply linear reductivity. -/
def NagataLinearlyReductiveSufficiencyStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      ((∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
          IsOpenImmersion i.hom.hom.left ∧
          Set.range i.hom.hom.left = IdentityComponent.identitySet G ∧
          IsMultiplicativeType H) ∧
        ¬ p ∣ Nat.card (IdentityComponent.GeometricComponents k G)) →
      IsLinearlyReductive G

/-- The three implications assemble to the exact unchanged Library target. -/
theorem nagataLinearlyReductive_of_parts
    (hidentity : NagataIdentityComponentNecessityStatement.{u})
    (horder : NagataComponentOrderNecessityStatement.{u})
    (hsufficiency : NagataLinearlyReductiveSufficiencyStatement.{u}) :
    NagataLinearlyReductiveStatement.{u} := by
  intro k _ p _ hp G _ _
  constructor
  · intro hG
    exact ⟨hidentity k p hp G hG, horder k p hp G hG⟩
  · exact hsufficiency k p hp G

/-- This is a purely logical decomposition; no structural part is proved here. -/
theorem nagataLinearlyReductive_iff_parts :
    NagataLinearlyReductiveStatement.{u} ↔
      NagataIdentityComponentNecessityStatement.{u} ∧
        NagataComponentOrderNecessityStatement.{u} ∧
          NagataLinearlyReductiveSufficiencyStatement.{u} := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro k _ p _ hp G _ _ hG
      exact ((h k p hp G).mp hG).1
    · intro k _ p _ hp G _ _ hG
      exact ((h k p hp G).mp hG).2
    · intro k _ p _ hp G _ _ hG
      exact (h k p hp G).mpr hG
  · rintro ⟨hi, ho, hs⟩
    exact nagataLinearlyReductive_of_parts hi ho hs

end Langlands.GroupScheme
