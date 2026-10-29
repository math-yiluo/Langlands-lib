import Langlands.Group.GL.UpperUnipotent
import Langlands.LocalField.Definitions
import Langlands.Representation.Category.Basic
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Jacquet.Localization
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

The finite-dimensionality part of the single-block case of Bernstein--Zelevinsky
(1976), §5.18 with Proposition 5.15(a) and Theorem 5.16 (printed pp.49--50), as
used in Theorem 7.12, step (5) (printed p.61). This is a proposition
definition, not a proof.
-/

namespace Langlands.Whittaker

universe uF uV

/-- For an irreducible supercuspidal smooth complex representation of the
actual `GL_m(F)` of positive rank, and every locally constant character of the
actual upper-unipotent subgroup, the actual character-localized coinvariant
quotient is finite-dimensional. The supplied topological data determines
smoothness, supercuspidality and local constancy. -/
def SupercuspidalCoinvariantFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (m : ℕ), 0 < m →
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier),
      σ.IsIrreducible → GeneralLinear.IsSupercuspidal σ.representation →
      ∀ η : GeneralLinear.upperUnipotent m F.Carrier →* ℂˣ,
        IsLocallyConstant (fun u => (η u : ℂ)) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants σ.representation
            (GeneralLinear.upperUnipotent m F.Carrier) η)

end Langlands.Whittaker
