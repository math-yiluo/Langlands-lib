import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-!
# Integral families of `GL_n` and `Res_{L/K} GL_n` on adelic points

Let `L/K` be a finite extension of number fields, `G = GL_n` over `K` and
`W = Res_{L/K} GL_n`.  The proposition `GeneralLinearIntegralFamilyTopologyStatement` says:

1. the family `localIntegralFamily K L n` (`GL_n(O_{E_v})` at the finite places `v`, the whole
   group at the infinite places) is uniformly integral: every regular function of `W` is
   integral on all of `GL_n(O_{E_v})` at almost every finite place `v`;
2. for every finite set `T` of places of `K`, the set of adelic points of `W` whose components
   outside `T` lie in `localIntegralFamily K L n`, and the set of adelic points of `G` whose
   components outside `T` lie in `glIntegralFamily K n`, are open.

These are consequences of the description of the adelic points of an affine algebraic group
as a restricted direct product (Getz–Hahn 2024, Proposition 2.3.1, printed p. 57).  The module
states the proposition and does not prove it.  See
`GeneralLinearIntegralFamilyTopologyStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism

local instance generalLinearIntegralFamilyIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearIntegralFamilySmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

set_option maxRecDepth 4000 in
/-- For number fields `K` and `L` with `L/K` finite and `n : ℕ`, with `GLₙ = GL_n` over `K`
and `Wₙ = Res_{L/K} GL_n`:

1. `localIntegralFamily K L n` is uniformly integral: for every regular function `a` of `Wₙ`,
   at all but finitely many finite places `v` of `K`, every element of
   `localIntegralSubgroup K L n v = GL_n(O_{E_v})` has `a`-value in
   `v.adicCompletionIntegers K`;
2. for every finite set `T` of places of `K`, the set of `x ∈ Wₙ(𝔸_K)` with
   `atPlace K Wₙ i x ∈ localIntegralFamily K L n i` for every place `i ∉ T` is open in
   `Wₙ(𝔸_K)`, and the set of `x ∈ GLₙ(𝔸_K)` with
   `atPlace K GLₙ i x ∈ glIntegralFamily K n i` for every place `i ∉ T` is open in
   `GLₙ(𝔸_K)`. -/
def GeneralLinearIntegralFamilyTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ),
    IsUniformlyIntegral K Wₙ (localIntegralFamily K L n) ∧
    ∀ T : Finset (Place K),
      IsOpen {x : AdelicGroupPoints K Wₙ |
        ∀ i : Place K, i ∉ T → atPlace K Wₙ i x ∈ localIntegralFamily K L n i} ∧
      IsOpen {x : AdelicGroupPoints K GLₙ |
        ∀ i : Place K, i ∉ T → atPlace K GLₙ i x ∈ glIntegralFamily K n i}

end Langlands.TraceFormula
