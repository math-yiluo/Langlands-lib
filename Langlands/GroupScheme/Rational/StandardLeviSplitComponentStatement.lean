import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.CharactersStatement

/-! # Split components in the actual standard Levi representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual standard Levi is connected reductive and has a split component whose
inclusion into the ambient group factors through the same maximal split torus. -/
def StandardLeviSplitComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
        IsConnectedReductive (Standard.leviScheme i ν J) ∧
          ∃ (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (a : A.toGrp ⟶ Standard.leviScheme i ν J) (g : A.toGrp ⟶ T.toGrp),
            IsSplitComponent a ∧ g ≫ i = a ≫ Standard.leviHom i ν J

/-- The standard-family target follows from the existing general structural targets.
This implication does not supply proofs of its three premises. -/
theorem standardLeviSplitComponent_of_structural_statements
    (hStd : StandardCocharacterStatement.{u}) (hSplit : SplitComponentStatement.{u})
    (hLevi : LeviSplitComponentStatement.{u}) :
    StandardLeviSplitComponentStatement.{u} := by
  intro k _ G hG T i hi ν hν J hJ
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcomparison⟩ := hStd k G hG T i hi ν hν J hJ
  have hrep :
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
        (Standard.leviHom i ν J) := by
    rw [← (hcomparison ζ hζ).2.1]
    exact Standard.isRepresentedBy_leviHom i ν J
  obtain ⟨hM, hA⟩ := hLevi k G hG T i hi ζ (Standard.leviScheme i ν J)
    (Standard.leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J) hrep
  obtain ⟨⟨A_G, iG, hiG⟩, _⟩ := hSplit k G hG
  obtain ⟨A, a, _, g, ha, _, hg, _⟩ := hA A_G iG hiG
  exact ⟨hM, A, a, g, ha, hg⟩

end Langlands.GroupScheme
