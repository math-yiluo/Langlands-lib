import Langlands.Representation.Archimedean.GKModule

/-!
# Reduction of the real generic standard-parameter statement

`RealGenericStandardParameterStatement` asks for a standard-module parameter of every
irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module `V`: an injective
`(𝔤, K)`-equivariant map from the `O(n)`-finite part of the Library's standard module
`realStandardModule n ds` into `V`. This file splits it into two statements:

* `RealLanglandsQuotientStatement` (the existence half of the Langlands classification,
  Knapp 1994, Theorem 1): every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a
  nonzero `(𝔤, K)`-equivariant map from the standard module of a list of real blocks of total
  rank `n` in Langlands order, that is, with non-increasing real parts of the exponents;
* `RealGenericLanglandsQuotientInjectiveStatement` (the standard module of a generic Langlands
  quotient is irreducible: Vogan's theorem for real groups, as reported by Casselman–Shahidi
  1998, p. 562, combined with a separate passage from the algebraic genericity used here to
  continuous Whittaker functionals, attributed to Kostant and Matumoto and not verified here):
  if moreover the module is generic, every such nonzero map is injective.

`realGenericStandardParameterReduction` proves that the two imply the target.
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

/-! ## Langlands order of real blocks -/

/-- The real part of the exponent of a real block: `Re t` for the character
`sgn^ε |·|^t` of `GL_1(ℝ)` and for the block `D ⊗ |det|^t` of `GL_2(ℝ)` induced from the
character `(z/|z|)^m |z|^(2t)` of `ℂ^×`. It is the real part of the exponent by which the
block's character `|·|^t` acts at each of its diagonal positions. -/
def realBlockExponent : RealBlock → ℝ
  | .character d => d.exponent.re
  | .induced d => d.exponent.re

/-- A list of real blocks is in Langlands order when the real parts of the exponents of its
blocks are non-increasing: a block never has a larger real exponent than a block before it.
For the upper triangular parabolic subgroup this is the closed positive chamber, in which
the standard module has a unique irreducible quotient (Knapp 1994, Theorem 1(a)). -/
def IsRealLanglandsOrdered (ds : List RealBlock) : Prop :=
  ds.Pairwise fun x y => realBlockExponent y ≤ realBlockExponent x

/-! ## Intertwiners out of real standard modules -/

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `B` is a `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
the real blocks `ds` into `(ρ, π)`: for every `k ∈ O(n)` and every `f`, the right translate
of `f` by `k` is again in that space and `B` carries it to `ρ(k)(B f)`; for every real `X`
and every `f`, the right derivative of `f` along `X` is again in that space and `B` carries
it to `π(1 ⊗ X)(B f)`. These are the last two clauses of `HasRealStandardParameter`. -/
def IsRealStandardIntertwiner (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ds : List RealBlock)
    (B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V) : Prop :=
  (∀ (k : unitaryCompact ℝ n)
      (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
    ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      B ⟨_, hf⟩ =
        ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (B f)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℝ)
      (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
    ∃ hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      B ⟨_, hf⟩ = π (1 ⊗ₜ X) (B f)

/-- A standard-module parameter is exactly an injective intertwiner out of a standard module
of the right rank. -/
theorem hasRealStandardParameter_iff (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ds : List RealBlock) :
    HasRealStandardParameter n ρ π ds ↔
      realRank ds = n ∧
        ∃ A : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
          Function.Injective A ∧ IsRealStandardIntertwiner n ρ π ds A :=
  Iff.rfl

/-! ## The two statements and the reduction -/

/-- The existence half of the Langlands classification of `GL_n(ℝ)` (Knapp 1994, Theorem 1),
for `(𝔤, K)`-modules and the Library's standard modules: every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` receives a nonzero intertwiner from the `O(n)`-finite
functions of the standard module of some list of real blocks of total rank `n` in Langlands
order. Since the module is irreducible, the intertwiner is onto: the module is the Langlands
quotient of that standard module. -/
def RealLanglandsQuotientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ ds : List RealBlock, realRank ds = n ∧ IsRealLanglandsOrdered ds ∧
        ∃ B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
          B ≠ 0 ∧ IsRealStandardIntertwiner n ρ π ds B

/-- The standard module of a generic Langlands quotient is irreducible, for `(𝔤, K)`-modules
and the Library's standard modules. For real groups this is Vogan's theorem (Invent. Math. 48,
1978), as reported by Casselman–Shahidi 1998, p. 562; that report concerns genericity in the
sense of continuous Whittaker functionals. The algebraic genericity `IsRealGenericGKModule`
used here needs a separate passage to continuous Whittaker functionals (Kostant 1978,
Matumoto 1987; not verified here). The statement: if `(ρ, π)` is an irreducible admissible generic
`(𝔤𝔩_n(ℝ), O(n))`-module and `ds` is a list of real blocks of total rank `n` in Langlands
order, then every nonzero intertwiner from the `O(n)`-finite functions of the standard module
of `ds` into `(ρ, π)` is injective. -/
def RealGenericLanglandsQuotientInjectiveStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ds : List RealBlock)
    (B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsRealGenericGKModule n π → realRank ds = n → IsRealLanglandsOrdered ds → B ≠ 0 →
        IsRealStandardIntertwiner n ρ π ds B → Function.Injective B

/-- The Langlands classification and the irreducibility of generic standard modules imply
that every irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module has a standard-module
parameter. -/
def RealGenericStandardParameterReductionStatement : Prop :=
  RealLanglandsQuotientStatement.{uV} →
    RealGenericLanglandsQuotientInjectiveStatement.{uV} →
      RealGenericStandardParameterStatement.{uV}

/-- The reduction: the nonzero intertwiner given by the Langlands classification is
injective by genericity, so it is a standard-module parameter. -/
theorem realGenericStandardParameterReduction :
    RealGenericStandardParameterReductionStatement.{uV} := by
  intro hA hB n V _ _ ρ π hgk hirr hadm hgen
  obtain ⟨ds, hrank, hord, B, hB0, hBint⟩ := hA n V ρ π hgk hirr hadm
  exact ⟨ds, hrank, B, hB n V ρ π ds B hgk hirr hadm hgen hrank hord hB0 hBint, hBint⟩

end Langlands.Archimedean
