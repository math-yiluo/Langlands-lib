import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.AffineWeilRestriction
import Mathlib.FieldTheory.Separable

/-! # Simply connected almost-simple groups as Weil restrictions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The simply connected form of Borel–Tits 6.21(ii): an almost-simple
simply connected group over an arbitrary field is a Weil restriction of
an absolutely almost-simple simply connected group over a finite separable
extension. This is a statement only. -/
def SimplyConnectedAlmostSimpleWeilRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsSimplyConnected G → IsAlmostSimple G →
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
        (_ : FiniteDimensional k K) (_ : Algebra.IsSeparable k K)
        (G' : GroupScheme (Spec (CommRingCat.of K)))
        (_ : IsAffine G'.X.left) (_ : LocallyOfFiniteType G'.X.hom),
        IsSimplyConnected G' ∧ IsAbsolutelyAlmostSimple G' ∧
          Nonempty (G ≅ AffineWeil.groupScheme k K G')

end Langlands.GroupScheme
