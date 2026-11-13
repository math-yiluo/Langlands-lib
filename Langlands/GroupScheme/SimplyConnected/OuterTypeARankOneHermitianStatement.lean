import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Examples.HermitianRootReflectionAction

/-!
# Actual Hermitian models from the rank-one outer-A index

This module states the identification of an arbitrary simply connected
absolutely almost-simple group with the actual Hermitian equalizer model,
given its actual outer-A rank-one index. The identification is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual outer-A indices with distinguished endpoints give a Hermitian
model with an anisotropic middle of dimension `n - 1`, over any field and in
every characteristic. This is an unproved identification statement; neither
an extension, a form nor a group-model isomorphism is supplied as a premise. -/
def OuterTypeARankOneHermitianStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      d.HasRankOneOuterAIndex n → splitRank G = 1 →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L)
        (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin (n - 1)))
        (w : Fin (n - 1) → Lˣ) (hw : ∀ i, (w i : L) = H.weight i),
        H.IsAnisotropic ∧
          Nonempty (G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw)

end Langlands.GroupScheme
