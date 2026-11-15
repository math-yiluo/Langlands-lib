import Langlands.Representation.Archimedean.RealLanglandsRankOneReduction

/-!
# The rank-one step from filtrations of standard modules

`RealRankOneStepStatement` concerns an irreducible module that receives a nonzero intertwiner
from the standard module of a list of real blocks `pre ++ x :: y :: post` with
`Re t(x) < Re t(y)`. This file reduces it to two statements about the standard modules
alone, with no target module.

A filtration of the `O(n)`-finite functions of the standard module of `pre ++ x :: y :: post`
is given here by finitely many linear maps `q 0, …, q (k - 1)` into it, from the
`O(n)`-finite functions of the standard modules of `pre ++ ws j ++ post`, such that the
ranges together span everything and each `q j` commutes with the action of `O(n)` and `𝔤`
modulo the span of the ranges of the earlier maps (`IsRealIntertwinerModulo`). Every `ws j`
is either `[y, x]` or a list of blocks with the exponent support of `[x, y]` up to order and
a strictly larger sum of squared weights (`RealAdjacentFiltration`).

The two statements ask for such a filtration when `x` and `y` are two characters
(`RealCharacterPairFiltrationStatement`, a statement about `GL_2(ℝ)` induced in stages) and
when at least one of them is an induced block (`RealInducedPairFiltrationStatement`).

`realRankOneStep_of_filtration` proves that the two imply `RealRankOneStepStatement`: a
nonzero intertwiner `B` out of the standard module of `pre ++ x :: y :: post` does not vanish
on all the ranges; on the first range where it does not vanish, `B ∘ q j` is a nonzero
intertwiner, because `B` kills the earlier ranges.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## Intertwiners modulo a subspace -/

/-- A linear map `q` from the `O(n)`-finite functions of the standard module of the real
blocks `ds` to those of the standard module of the real blocks `es` is an intertwiner modulo
the subspace `M` of the target: for every `k ∈ O(n)` and every `f`, the right translates by
`k` of `f` and of `q f` are again in the respective spaces, and `q` of the first differs from
the second by an element of `M`; likewise for the right derivative along every real `X`.
For `M = ⊥` these are the clauses of `IsRealStandardIntertwiner`, with the target module
being the standard module of `es`. -/
def IsRealIntertwinerModulo (n : ℕ) (ds es : List RealBlock)
    (M : Submodule ℂ (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)))
    (q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) : Prop :=
  (∀ (k : unitaryCompact ℝ n)
      (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
    ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      ∃ hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (q f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
        q ⟨_, hf⟩ - ⟨_, hg⟩ ∈ M) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℝ)
      (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
    ∃ hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      ∃ hg : rightDerivative (matrixModel ℝ n) X (q f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
        q ⟨_, hf⟩ - ⟨_, hg⟩ ∈ M

/-- An intertwiner `B` out of the standard module of `es` that vanishes on `M`, composed with
an intertwiner modulo `M` from the standard module of `ds`, is an intertwiner out of the
standard module of `ds`. -/
theorem IsRealIntertwinerModulo.comp {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {ds es : List RealBlock}
    {M : Submodule ℂ (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))}
    {q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    {B : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) →ₗ[ℂ] V}
    (hq : IsRealIntertwinerModulo n ds es M q) (hB : IsRealStandardIntertwiner n ρ π es B)
    (hM : M ≤ LinearMap.ker B) : IsRealStandardIntertwiner n ρ π ds (B ∘ₗ q) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hmem⟩ := hq.1 k f
    obtain ⟨hg', hB'⟩ := hB.1 k (q f)
    refine ⟨hf, ?_⟩
    have h0 : B (q ⟨_, hf⟩ - ⟨_, hg⟩) = 0 := hM hmem
    rw [map_sub, sub_eq_zero] at h0
    simpa [LinearMap.comp_apply, h0] using hB'
  · obtain ⟨hf, hg, hmem⟩ := hq.2 X f
    obtain ⟨hg', hB'⟩ := hB.2 X (q f)
    refine ⟨hf, ?_⟩
    have h0 : B (q ⟨_, hf⟩ - ⟨_, hg⟩) = 0 := hM hmem
    rw [map_sub, sub_eq_zero] at h0
    simpa [LinearMap.comp_apply, h0] using hB'

/-! ## Filtrations of the standard module of an adjacent pair -/

/-- A filtration of the standard module of `pre ++ x :: y :: post` adapted to the rank-one
step. There are `k` lists of real blocks `ws j` and linear maps `q j` from the `O(n)`-finite
functions of the standard module of `pre ++ ws j ++ post` to those of the standard module of
`pre ++ x :: y :: post` such that

* every `ws j` is `[y, x]`, or its exponent support is a permutation of that of `[x, y]` and
  its sum of squared weights is strictly larger than that of `[x, y]`;
* every `q j` is an intertwiner modulo the span of the ranges of the `q i` with `i < j`;
* the ranges of all the `q j` span the whole space.

The spans `F_j` of the ranges of `q 0, …, q (j - 1)` then form a filtration by
`(𝔤, K)`-submodules whose `j`-th graded piece `F_(j+1)/F_j` is a quotient of the standard
module of `pre ++ ws j ++ post`, `q j` being a linear lift of the quotient map. -/
def RealAdjacentFiltration (n : ℕ) (pre post : List RealBlock) (x y : RealBlock) : Prop :=
  ∃ (k : ℕ) (ws : Fin k → List RealBlock)
    (q : ∀ j : Fin k,
      kFiniteFunctions (realStandardModule n (pre ++ ws j ++ post)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n (pre ++ x :: y :: post)) (unitaryCompact ℝ n)),
    (∀ j, ws j = [y, x] ∨
      ((realExponentSupport (ws j)).Perm (realExponentSupport [x, y]) ∧
        realWeightSquareSum [x, y] < realWeightSquareSum (ws j))) ∧
    (∀ j, IsRealIntertwinerModulo n (pre ++ ws j ++ post) (pre ++ x :: y :: post)
      (⨆ (i : Fin k) (_ : i < j), LinearMap.range (q i)) (q j)) ∧
    ⨆ j, LinearMap.range (q j) = ⊤

/-- The filtration of the rank-one step for two characters. Let `pre ++ x :: y :: post` be a
list of real blocks of total rank `n` in which `x` and `y` are characters of `GL_1(ℝ)` with
`Re t(x) < Re t(y)`. Then the standard module of `pre ++ x :: y :: post` has a filtration as
in `RealAdjacentFiltration`. -/
def RealCharacterPairFiltrationStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (c d : RealCharacterData),
    realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n →
    realBlockExponent (RealBlock.character c) < realBlockExponent (RealBlock.character d) →
      RealAdjacentFiltration n pre post (RealBlock.character c) (RealBlock.character d)

/-- The filtration of the rank-one step when an induced block is involved. Let
`pre ++ x :: y :: post` be a list of real blocks of total rank `n` in which `x` or `y` is a
real induction of a character of `ℂ^×`, with `Re t(x) < Re t(y)`. Then the standard module of
`pre ++ x :: y :: post` has a filtration as in `RealAdjacentFiltration`. -/
def RealInducedPairFiltrationStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (x y : RealBlock),
    ((∃ d, x = RealBlock.induced d) ∨ ∃ d, y = RealBlock.induced d) →
    realRank (pre ++ x :: y :: post) = n →
    realBlockExponent x < realBlockExponent y →
      RealAdjacentFiltration n pre post x y

/-- The two filtration statements imply the rank-one step. -/
def RealRankOneStepFromFiltrationStatement : Prop :=
  RealCharacterPairFiltrationStatement → RealInducedPairFiltrationStatement →
    RealRankOneStepStatement.{uV}

/-! ## The reduction -/

/-- Every adjacent pair of real blocks has a filtration, given both filtration statements. -/
theorem realAdjacentFiltration_of_statements (hC : RealCharacterPairFiltrationStatement)
    (hI : RealInducedPairFiltrationStatement) (n : ℕ) (pre post : List RealBlock)
    (x y : RealBlock) (hrank : realRank (pre ++ x :: y :: post) = n)
    (hxy : realBlockExponent x < realBlockExponent y) : RealAdjacentFiltration n pre post x y := by
  cases x with
  | induced c => exact hI n pre post _ y (Or.inl ⟨c, rfl⟩) hrank hxy
  | character c =>
      cases y with
      | induced d => exact hI n pre post _ _ (Or.inr ⟨d, rfl⟩) hrank hxy
      | character d => exact hC n pre post c d hrank hxy

/-- The conclusion of the rank-one step from a nonzero intertwiner out of the standard module
of `pre ++ ws ++ post`, for a list `ws` allowed in `RealAdjacentFiltration`. -/
theorem realRankOneStep_conclusion_of_mem {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {pre post : List RealBlock}
    {x y : RealBlock} {ws : List RealBlock}
    (hws : ws = [y, x] ∨ ((realExponentSupport ws).Perm (realExponentSupport [x, y]) ∧
      realWeightSquareSum [x, y] < realWeightSquareSum ws))
    (B : kFiniteFunctions (realStandardModule n (pre ++ ws ++ post)) (unitaryCompact ℝ n) →ₗ[ℂ] V)
    (hB0 : B ≠ 0) (hB : IsRealStandardIntertwiner n ρ π (pre ++ ws ++ post) B) :
    (∃ B' : kFiniteFunctions (realStandardModule n (pre ++ y :: x :: post))
        (unitaryCompact ℝ n) →ₗ[ℂ] V,
      B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (pre ++ y :: x :: post) B') ∨
    ∃ zs : List RealBlock,
      (realExponentSupport zs).Perm (realExponentSupport [x, y]) ∧
      realWeightSquareSum [x, y] < realWeightSquareSum zs ∧
      ∃ B' : kFiniteFunctions (realStandardModule n (pre ++ zs ++ post))
          (unitaryCompact ℝ n) →ₗ[ℂ] V,
        B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (pre ++ zs ++ post) B' := by
  rcases hws with rfl | ⟨hperm, hlt⟩
  · left
    have h : ∃ B' : kFiniteFunctions (realStandardModule n (pre ++ [y, x] ++ post))
        (unitaryCompact ℝ n) →ₗ[ℂ] V,
        B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (pre ++ [y, x] ++ post) B' := ⟨B, hB0, hB⟩
    rwa [show pre ++ [y, x] ++ post = pre ++ y :: x :: post by simp] at h
  · exact Or.inr ⟨ws, hperm, hlt, B, hB0, hB⟩

/-- The reduction of the rank-one step to the two filtration statements. Given the filtration
`q` of the standard module of `pre ++ x :: y :: post` and a nonzero intertwiner `B` out of it,
take the first `j` with `B ∘ q j ≠ 0`; it exists since the ranges of the `q j` span
everything. `B` vanishes on the ranges of the earlier `q i`, so `B ∘ q j` is an intertwiner
out of the standard module of `pre ++ ws j ++ post`. -/
theorem realRankOneStep_of_filtration : RealRankOneStepFromFiltrationStatement.{uV} := by
  intro hC hI n V _ _ ρ π pre post x y B _ _ _ hrank hxy hB0 hB
  obtain ⟨k, ws, q, hws, hq, hspan⟩ :=
    realAdjacentFiltration_of_statements hC hI n pre post x y hrank hxy
  have hex : ∃ j, B ∘ₗ q j ≠ 0 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply hB0
    have htop : (⊤ : Submodule ℂ _) ≤ LinearMap.ker B := by
      rw [← hspan]
      exact iSup_le fun j => LinearMap.range_le_ker_iff.2 (hnone j)
    exact LinearMap.ker_eq_top.1 (top_le_iff.1 htop)
  let S : Set (Fin k) := {j | B ∘ₗ q j ≠ 0}
  have hS : S.Nonempty := hex
  set j := WellFounded.min wellFounded_lt S hS with hj
  have hjS : B ∘ₗ q j ≠ 0 := WellFounded.min_mem wellFounded_lt S hS
  have hbefore : ∀ i, i < j → B ∘ₗ q i = 0 := by
    intro i hi
    by_contra hne
    exact WellFounded.not_lt_min wellFounded_lt S hne hi
  have hM : (⨆ (i : Fin k) (_ : i < j), LinearMap.range (q i)) ≤ LinearMap.ker B :=
    iSup_le fun i => iSup_le fun hi => LinearMap.range_le_ker_iff.2 (hbefore i hi)
  exact realRankOneStep_conclusion_of_mem (hws j) (B ∘ₗ q j) hjS ((hq j).comp hB hM)

end Langlands.Archimedean
