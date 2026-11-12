import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Lang–Weil estimate, uniformly in families over the integers

For a morphism `f : X ⟶ S` of finite type, with `S` of finite type over `ℤ`, whose fibres are
geometrically irreducible of dimension `d`, the number of `κ`-points of `X` lying over a
`κ`-point of `S` differs from `(#κ) ^ d` by at most `C (#κ) ^ (d - 1/2)`, with one constant `C`
for all finite fields `κ` and all `κ`-points of `S`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform Lang–Weil estimate for families with fibres of dimension `d`: for every
morphism `f : X ⟶ S` locally of finite type and quasi-compact, with `S` of finite type over
`ℤ`, that is geometrically irreducible (every fibre is geometrically irreducible) and whose
fibres have pure dimension `d`, there is `C > 0` such that for every finite field `κ` and every
`κ`-point `s` of `S`, the number `N_s` of `κ`-points `x` of `X` with `f ∘ x = s` satisfies
`|N_s - (#κ) ^ d| ≤ C (#κ) ^ (d - 1/2)`. -/
def FamilyLangWeilInDimension (d : ℕ) : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from S) → CompactSpace S →
    LocallyOfFiniteType f → QuasiCompact f → GeometricallyIrreducible f →
    (∀ s : S, SchemeFiberGeometry.HasPureDimension (f.fiber s) d) →
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ]
      (s : Spec (CommRingCat.of κ) ⟶ S),
      |(Nat.card {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = s} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2)

/-- The uniform Lang–Weil estimate for families over the integers, in every fibre dimension
`d`. -/
def FamilyLangWeilStatement : Prop :=
  ∀ d : ℕ, FamilyLangWeilInDimension.{u} d

end Langlands.AlgebraicGeometry.LangWeil
