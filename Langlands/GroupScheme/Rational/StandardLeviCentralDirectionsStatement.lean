import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Standard Levi split components and simple-root annihilators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- A subset of the actual simple roots cuts out a real cocharacter subspace
whose codimension is the number of selected roots. -/
def StandardRootAnnihilatorRankStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      Finite J ∧
      Module.Finite ℝ (V T) ∧
      Module.Finite ℝ (rootAnnihilator T J) ∧
      Module.finrank ℝ (V T) = splitTorusRank T ∧
      Module.finrank ℝ (rootAnnihilator T J) + Nat.card J = splitTorusRank T

/-- For each actual closed representative of a standard Levi, every split
component embeds into the chosen maximal split torus with image the selected
simple-root annihilator on real cocharacters. -/
def StandardLeviSplitCentralDirectionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j →
      (standardLevi i ν J).IsRepresentedBy j →
      IsConnectedReductive L ∧
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
        IsSplitComponent a →
        Module.Finite ℝ (V A) ∧
        ∃ f : A ⟶ T,
          CommGroupScheme.groupHom f ≫ i = a ≫ j ∧
          IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
          Function.Injective (cocharacterMapReal f) ∧
          (cocharacterMapReal f).range = rootAnnihilator T J ∧
          Module.finrank ℝ (rootAnnihilator T J) = splitTorusRank A ∧
          splitTorusRank T = Nat.card J + splitTorusRank A ∧
          rationalCharacterRank L = splitTorusRank A

/-- Intrinsic standard-Levi annihilator and rank targets, including their
realization by actual split components. -/
def StandardLeviCentralDirectionsStatement : Prop :=
  StandardRootAnnihilatorRankStatement.{u} ∧
    StandardLeviSplitCentralDirectionsStatement.{u}

end Langlands.GroupScheme
