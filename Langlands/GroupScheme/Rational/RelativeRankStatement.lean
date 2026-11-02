import Langlands.GroupScheme.Rational.RelativeRank

/-! # Intrinsic relative simple-root basis and rank targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

/-- For a maximal split torus of an actual connected reductive group and a generic
cocharacter, the actual simple relative roots form a rational basis of the relative
root span. Nonreduced root systems and the empty basis are included. -/
def RelativeSimpleRootBasisStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
      Finite (simpleRelativeRoots i ν) ∧
      (∃ b : Module.Basis (simpleRelativeRoots i ν) ℚ (relativeRootSpan i),
        ∀ α, b α = simpleRelativeRootVector i ν α) ∧
      relativeRootRank i = Nat.card (simpleRelativeRoots i ν)

/-- The full split rank is the relative root rank plus the rational-character
rank, which is also the rank of every actual split component. Restriction to that
component becomes an isomorphism after tensoring with `ℚ`. -/
def RelativeRankIdentityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    Module.Finite ℚ (ℚ ⊗[ℤ] characterLattice T) ∧
    Module.Finite ℚ (relativeRootSpan i) ∧
    Module.Finite ℚ (ℚ ⊗[ℤ] rationalCharacters G) ∧
    splitRank G = (splitTorusRank T : ℕ∞) ∧
    splitTorusRank T = relativeRootRank i + rationalCharacterRank G ∧
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsSplitComponent a →
      Module.Finite ℚ (ℚ ⊗[ℤ] characterLattice A) ∧
      Function.Bijective (rationalCharacterRestrictRat a) ∧
      rationalCharacterRank G = splitTorusRank A ∧
      splitTorusRank T = relativeRootRank i + splitTorusRank A

/-- The intrinsic simple-root basis and full-rank identities, with no
root-system or Coxeter-realization premise. -/
def RelativeRankStatement : Prop :=
  RelativeSimpleRootBasisStatement.{u} ∧ RelativeRankIdentityStatement.{u}

end Langlands.GroupScheme
