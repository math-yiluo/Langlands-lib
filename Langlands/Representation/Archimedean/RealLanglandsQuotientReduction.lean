import Langlands.Representation.Archimedean.RealGenericParameterReduction

/-!
# Reduction of the real Langlands quotient statement

`RealLanglandsQuotientStatement` asks that every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module receive a nonzero intertwiner from the `O(n)`-finite functions of
the standard module of a list of real blocks of total rank `n` in Langlands order. This file
splits it into two statements:

* `RealPrincipalSeriesQuotientStatement` (Casselman's subrepresentation theorem, in quotient
  form): every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero intertwiner
  from the `O(n)`-finite principal series of some `n` characters of `ℝ^×`, in any order. The
  principal series is the Library's standard module of the list of those characters, each a
  block of rank one.
* `RealLanglandsFromPrincipalSeriesStatement` (the Langlands classification, starting from a
  principal-series quotient): if an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a
  nonzero intertwiner from such a principal series, then it receives a nonzero intertwiner from
  the standard module of a list of real blocks of total rank `n` in Langlands order.

`realLanglandsQuotientReduction` proves that the two imply the target.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

/-- A list of real characters, read as real blocks of rank one, has total rank its length; so
the principal series in `RealPrincipalSeriesQuotientStatement` is the standard module of a list
of real blocks of total rank `n`. -/
theorem realRank_map_character (cs : List RealCharacterData) :
    realRank (cs.map RealBlock.character) = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [List.map_cons, realRank_cons, ih, List.length_cons]
      simp only [RealBlock.rank]
      omega

/-- Casselman's subrepresentation theorem for `GL_n(ℝ)`, in quotient form, for
`(𝔤, K)`-modules and the Library's principal series: every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a nonzero intertwiner from the `O(n)`-finite
functions of the standard module of some list of `n` real characters. That standard module is
the smooth principal series `principalSeries ℝ n` of those characters, in the order of the
list, normalized by the square root of the modulus character of the upper triangular Borel
subgroup; no order condition is imposed. -/
def RealPrincipalSeriesQuotientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ cs : List RealCharacterData, cs.length = n ∧
        ∃ B : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
            (unitaryCompact ℝ n) →ₗ[ℂ] V,
          B ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B

/-- The Langlands classification of `GL_n(ℝ)` (existence half), starting from a quotient of a
principal series: if an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a
nonzero intertwiner from the `O(n)`-finite functions of the standard module of a list of `n`
real characters (a principal series, in any order), then it receives a nonzero intertwiner from
the `O(n)`-finite functions of the standard module of some list of real blocks of total rank `n`
in Langlands order. -/
def RealLanglandsFromPrincipalSeriesStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (cs : List RealCharacterData)
    (B : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
      (unitaryCompact ℝ n) →ₗ[ℂ] V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      cs.length = n → B ≠ 0 → IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B →
        ∃ ds : List RealBlock, realRank ds = n ∧ IsRealLanglandsOrdered ds ∧
          ∃ B' : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
            B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π ds B'

/-- Casselman's theorem and the Langlands classification starting from a principal-series
quotient imply the Langlands quotient statement. -/
def RealLanglandsQuotientReductionStatement : Prop :=
  RealPrincipalSeriesQuotientStatement.{uV} →
    RealLanglandsFromPrincipalSeriesStatement.{uV} →
      RealLanglandsQuotientStatement.{uV}

/-- The reduction: Casselman's theorem gives a nonzero intertwiner from a principal series,
and the second statement turns it into one from a standard module in Langlands order. -/
theorem realLanglandsQuotientReduction :
    RealLanglandsQuotientReductionStatement.{uV} := by
  intro hC hL n V _ _ ρ π hgk hirr hadm
  obtain ⟨cs, hlen, B, hB0, hBint⟩ := hC n V ρ π hgk hirr hadm
  exact hL n V ρ π cs B hgk hirr hadm hlen hB0 hBint

end Langlands.Archimedean
