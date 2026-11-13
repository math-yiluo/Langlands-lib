import Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Finite twisted coinvariants of irreducible cuspidal Levi representations

The finite-dimensionality part of the cuspidal-Levi coefficient step in the
proof of Bernstein--Zelevinsky (1976), Theorem 7.12, step (5), printed p.61.
This is a proposition definition, not a proof.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding LeviCuspidalCoinvariantFinitenessStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- For an irreducible cuspidal smooth complex representation of an actual
standard product Levi of positive rank, and every locally constant character
of the product of the blockwise upper-unipotent subgroups, the actual
character-localized coinvariant quotient is finite-dimensional. The supplied
topological data determines smoothness, cuspidality and local constancy. -/
def LeviCuspidalCoinvariantFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      σ.IsIrreducible → CuspidalSupport.IsLeviCuspidal B σ.representation →
      ∀ η : (Subgroup.pi Set.univ
          (fun i : Fin B.length =>
            GeneralLinear.upperUnipotent (B.size i) F)) →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants σ.representation
            (Subgroup.pi Set.univ
              (fun i : Fin B.length =>
                GeneralLinear.upperUnipotent (B.size i) F)) η)

end Langlands.AllField.Whittaker
