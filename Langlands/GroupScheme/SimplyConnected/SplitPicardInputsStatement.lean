import Langlands.GroupScheme.SimplyConnected.SplitPicardTrivialStatement

/-! # Geometric inputs for the split semisimple Picard criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The character-lifting consequence of Milne 18.18: for a central isogeny of split
connected reductive groups, triviality of the target Picard group makes restriction
from source characters onto characters of the full scheme-theoretic kernel surjective. -/
def SplitCentralIsogenyPicardCharacterLiftingStatement : Prop :=
  ∀ (k : Type u) [Field k] (H G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive H → IsConnectedReductive G →
      HasSplitMaximalTorus H → HasSplitMaximalTorus G →
        ∀ (f : H ⟶ G), IsCentralIsogeny f →
          (∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
            Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial G.X.left)) →
          Function.Surjective (characterRestrict (kernelι f))

/-- Iversen's Picard-trivial isogeny (Milne 18.22), specialized to split semisimple
field groups. The source is again semisimple and the isogeny is central. -/
def SplitSemisimplePicardTrivialCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → HasSplitMaximalTorus G →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (f : H ⟶ G),
        IsSemisimple H ∧ IsCentralIsogeny f ∧
          ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle H.X.left,
            Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial H.X.left)

/-- The two geometric inputs used in Milne's split semisimple Picard criterion.
This conjunction asserts no proof of either input. -/
def SplitSemisimplePicardGeometricInputsStatement : Prop :=
  SplitCentralIsogenyPicardCharacterLiftingStatement.{u} ∧
    SplitSemisimplePicardTrivialCoverStatement.{u}

end Langlands.GroupScheme
