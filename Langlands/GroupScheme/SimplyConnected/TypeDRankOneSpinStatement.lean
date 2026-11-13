import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.GroupSchemes

/-!
# Actual quaternionic spin covers from rank-one type-D indices

This module states an unproved identification of an arbitrary simply connected
absolutely almost-simple group from its actual rank-one type-D index
`²D_4,1^(2)` or `¹D_5,1^(2)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual indices `²D_4,1^(2)` (with `n = 4`) and `¹D_5,1^(2)` (with `n = 5`)
give a spin cover of the isometry group of a nondegenerate quaternionic
`σ`-quadratic form of Witt index one in `n` variables, over any field. The
algebra, involution, form and actual spin-cover morphism are conclusions.
This identification statement is not proved here. -/
def TypeDRankOneSpinStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      ((n = 4 ∧ d.HasRankOneOuterD4Index) ∨ (n = 5 ∧ d.HasRankOneInnerD5Index)) →
      splitRank G = 1 →
      ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
        Module.finrank K D = 4 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = 3 ∧
              ∃ q : σ.QuadraticForms (Fin n),
                σ.IsNondegenerateQuadratic q ∧ σ.quadraticWittIndex q = 1 ∧
                  ∃ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π

end Langlands.GroupScheme
