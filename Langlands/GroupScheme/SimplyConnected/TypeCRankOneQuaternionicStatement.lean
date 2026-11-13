import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.GroupSchemes

/-!
# Actual quaternionic symplectic models from rank-one type-C indices

This module states an unproved identification of an arbitrary simply connected
absolutely almost-simple group from its actual rank-one type-C index.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual indices `C_2,1^(2)` and `C_3,1^(2)` give quaternionic symplectic
models in the same number of variables, over any field. The algebra,
involution, form and actual group-scheme isomorphism are conclusions.
This identification statement is not proved here. -/
def TypeCRankOneQuaternionicStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      d.HasRankOneCIndex n → splitRank G = 1 →
      ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
        Module.finrank K D = 4 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = 3 ∧
              ∃ (_ : NeZero n) (H : Matrix (Fin n) (Fin n) D),
                σ.IsAntihermitian H ∧ IsUnit H ∧ σ.wittIndex H = 1 ∧
                  Nonempty (G ≅ σ.symplecticGroup H)

end Langlands.GroupScheme
