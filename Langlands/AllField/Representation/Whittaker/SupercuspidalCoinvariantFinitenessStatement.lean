import Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

The finite-dimensionality part of the single-block case of Bernstein--Zelevinsky
(1976), §5.18 with Proposition 5.15(a) and Theorem 5.16 (printed pp.49--50), as
used in Theorem 7.12, step (5) (printed p.61). This is a proposition
definition, not a proof.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding SupercuspidalCoinvariantFinitenessStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- For an irreducible supercuspidal smooth complex representation of the
actual `GL_m(F)` of positive rank, and every locally constant character of the
actual upper-unipotent subgroup, the actual character-localized coinvariant
quotient is finite-dimensional. The supplied topological data determines
smoothness, supercuspidality and local constancy. -/
def SupercuspidalCoinvariantFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (m : ℕ), 0 < m →
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F),
      σ.IsIrreducible → GeneralLinear.IsSupercuspidal σ.representation →
      ∀ η : GeneralLinear.upperUnipotent m F →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants σ.representation
            (GeneralLinear.upperUnipotent m F) η)

end Langlands.AllField.Whittaker
