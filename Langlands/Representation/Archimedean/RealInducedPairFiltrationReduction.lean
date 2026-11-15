import Langlands.Representation.Archimedean.RealRankOneStepFiltration

/-!
# The induced-pair filtration from `GL₃(ℝ)`, `GL₄(ℝ)` and induction in stages

`RealInducedPairFiltrationStatement` asks for a filtration (`RealAdjacentFiltration`) of the
`O(n)`-finite functions of the standard module of `pre ++ x :: y :: post` when `x` or `y` is an
induction block and `Re t(x) < Re t(y)`. This file splits it into four statements:

* `RealAdjacentFiltrationInStagesStatement`: a filtration for the pair `[x, y]` alone, on
  `GL_r(ℝ)` with `r = realRank [x, y]` and `pre = post = []`, gives one for every `pre` and
  `post` (induction in stages);
* `RealCharacterInducedFiltrationStatement` and `RealInducedCharacterFiltrationStatement`: the
  filtration on `GL₃(ℝ)` for a character and an induction block, in either order;
* `RealInducedInducedFiltrationStatement`: the filtration on `GL₄(ℝ)` for two induction blocks.

`realInducedPairFiltration_of_base` proves that the four imply
`RealInducedPairFiltrationStatement`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-! ## Induction in stages -/

/-- Induction in stages of adjacent filtrations. Let `pre ++ x :: y :: post` be a list of real
blocks of total rank `n`. A filtration as in `RealAdjacentFiltration` of the standard module of
`[x, y]` on `GL_r(ℝ)`, `r = realRank [x, y]`, gives one of the standard module of
`pre ++ x :: y :: post` on `GL_n(ℝ)`. No condition on the exponents is assumed. -/
def RealAdjacentFiltrationInStagesStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (x y : RealBlock),
    realRank (pre ++ x :: y :: post) = n →
    RealAdjacentFiltration (realRank [x, y]) [] [] x y →
      RealAdjacentFiltration n pre post x y

/-! ## The base cases on `GL₃(ℝ)` and `GL₄(ℝ)` -/

/-- The filtration on `GL₃(ℝ)` of the standard module of a character `c` followed by an
induction block `d`, when `Re t(c) < Re t(d)`. -/
def RealCharacterInducedFiltrationStatement : Prop :=
  ∀ (c : RealCharacterData) (d : ComplexCharacterData),
    realBlockExponent (RealBlock.character c) < realBlockExponent (RealBlock.induced d) →
      RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d)

/-- The filtration on `GL₃(ℝ)` of the standard module of an induction block `d` followed by a
character `c`, when `Re t(d) < Re t(c)`. -/
def RealInducedCharacterFiltrationStatement : Prop :=
  ∀ (d : ComplexCharacterData) (c : RealCharacterData),
    realBlockExponent (RealBlock.induced d) < realBlockExponent (RealBlock.character c) →
      RealAdjacentFiltration 3 [] [] (RealBlock.induced d) (RealBlock.character c)

/-- The filtration on `GL₄(ℝ)` of the standard module of two induction blocks `d`, `e`, when
`Re t(d) < Re t(e)`. -/
def RealInducedInducedFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData),
    realBlockExponent (RealBlock.induced d) < realBlockExponent (RealBlock.induced e) →
      RealAdjacentFiltration 4 [] [] (RealBlock.induced d) (RealBlock.induced e)

/-! ## The reduction -/

/-- Induction in stages and the three base cases on `GL₃(ℝ)` and `GL₄(ℝ)` imply
`RealInducedPairFiltrationStatement`. -/
theorem realInducedPairFiltration_of_base (hS : RealAdjacentFiltrationInStagesStatement)
    (hCI : RealCharacterInducedFiltrationStatement)
    (hIC : RealInducedCharacterFiltrationStatement)
    (hII : RealInducedInducedFiltrationStatement) : RealInducedPairFiltrationStatement := by
  intro n pre post x y hind hrank hxy
  refine hS n pre post x y hrank ?_
  cases x with
  | character c =>
      cases y with
      | character d =>
          exfalso
          rcases hind with ⟨e, he⟩ | ⟨e, he⟩ <;> cases he
      | induced d => exact hCI c d hxy
  | induced d =>
      cases y with
      | character c => exact hIC d c hxy
      | induced e => exact hII d e hxy

end Langlands.Archimedean
