import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Structural targets for split torus actions without a zero Lie weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- CGP's general observation in the proof of Proposition 2.3.11: a smooth
connected affine group with no zero Lie weight for a split torus action is
unipotent. The eigenspace is the actual all-coefficient Lie eigenspace. -/
def TorusActionUnipotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    (_hSmooth : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom)
    (_hConn : ConnectedSpace H.X.left)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp H,
      letI := hAff
      actionWeightSpace b 0 = ⊥ → IsUnipotent H

/-- The splitness argument of CGP Lemma 3.3.8 for any smooth connected
unipotent affine group with no zero Lie weight for a split torus action.
Splitness is the published finite normal Ga-series on all scheme tests. -/
def TorusActionSplitUnipotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    (_hSmooth : Smooth H.X.hom) (hAff : IsAffineHom H.X.hom)
    (_hConn : ConnectedSpace H.X.left) (_hUnipotent : IsUnipotent H)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp H,
      letI := hAff
      actionWeightSpace b 0 = ⊥ → IsSplitUnipotent H

/-- The two independent structural proof obligations used to obtain unipotence
and a finite Ga-series from the absence of zero Lie weights. -/
def TorusActionUnipotenceStructureStatement : Prop :=
  TorusActionUnipotenceStatement.{u} ∧ TorusActionSplitUnipotenceStatement.{u}

end Langlands.GroupScheme.RelativeRoot
