import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A uniform Lang–Weil estimate for smooth families over the integers

Conrad's Lemma 4.6: for a smooth separated surjective map of schemes of finite type over
`ℤ` whose fibres are geometrically connected of dimension `d`, the number of rational points of
the fibre over a closed point `b` differs from `q_b ^ d` by at most `C q_b ^ (d - 1/2)`, with one
constant `C` for all closed points.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Conrad's Lemma 4.6 (printed p.12): let `f : Y ⟶ B` be a smooth, separated, surjective map
of finite type, with `B` of finite type over `ℤ`, whose fibres are geometrically connected and
of pure dimension `d`. Then there is `C > 0` such that for every closed point `b` of `B`, with
`q_b` the cardinality of its residue field, the number `N_b` of rational points of the fibre
over `b` satisfies `|N_b - q_b ^ d| ≤ C q_b ^ (d - 1/2)`. -/
def UniformLangWeilStatement : Prop :=
  ∀ (B Y : Scheme.{u}) (f : Y ⟶ B) (d : ℕ),
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B) → CompactSpace B →
    Smooth f → _root_.AlgebraicGeometry.IsSeparated f → Surjective f →
    LocallyOfFiniteType f → QuasiCompact f → GeometricallyConnected f →
    (∀ b : B, SchemeFiberGeometry.HasPureDimension (f.fiber b) d) →
    ∃ C : ℝ, 0 < C ∧ ∀ b : B, IsClosed ({b} : Set B) →
      |(Nat.card {s : Spec (B.residueField b) ⟶ f.fiber b //
            s ≫ f.fiberToSpecResidueField b = 𝟙 _} : ℝ) -
          (Nat.card (B.residueField b) : ℝ) ^ d| ≤
        C * (Nat.card (B.residueField b) : ℝ) ^ ((d : ℝ) - 1 / 2)

end Langlands.AlgebraicGeometry
