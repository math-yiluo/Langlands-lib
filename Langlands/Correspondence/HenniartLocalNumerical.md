# Weil-side numerical invariants of nonarchimedean local fields

`Langlands.Henniart.LocalNumerical` takes a nonarchimedean local field `K`
with Mathlib's valuative relation and topology and a separable closure `Ω`
of `K`. It uses the published group, geometric degree and unramified
characters in `Langlands.Weil.Local.SepClosed` and the finite inertia
presentations in `Langlands.Ramification.Local.SepClosed`. The field, closure
and complex representation carriers have independent universe levels.

## Classes, twists and conductors

- `IrreducibleWeilClass K Ω n` is the class space `G⁰_K(n)` of Henniart
  1988, §1.1, for positive `n`. Its classes are isomorphism classes of
  continuous irreducible complex representations of the Weil group of
  `Ω/K`. `weilClassForget K Ω σ` projects to the underlying representation
  isomorphism class by forgetting the rank and the continuous and irreducible
  conditions. This projection uses the Library's `forgetPropertyClass`.
- `weilUnramifiedTwist K Ω k z` is the equivalence on rank `k + 1` classes
  given by multiplying the action of an element of geometric degree `m`
  by `z ^ m`. The degree is one at geometric Frobenius, so `z : ℂˣ`
  records the character's value there. This gives the unramified twist
  in the geometric normalization of Henniart 1988, §1.2.
- `HasArtinConductor K Ω σ a` means that a representative of `σ` admits
  a finite inertia presentation with surjective Weil inertia restriction
  and Artin expression equal to `(a : ℚ)` for `a : ℕ`. The expression is
  Serre's sum of the fixed-space codimensions weighted by
  `|Gᵢ| / |G₀|` over the lower ramification groups, starting at index
  zero. The existential records the representative, the presentation and
  surjectivity, using the same class map as `weilClassForget`. It formalizes
  the Artin exponent of Henniart 1988, §1.2, through the Library's finite
  presentation interface.
- `weilOrbitStratum K Ω k a` is the set of unramified-twist orbits
  containing a rank `k + 1` class satisfying `HasArtinConductor K Ω σ a`.
  This is `Wᴀʳᵗ_K(k+1,a)` of the route note, §2.1. The orbit map takes
  the rank-tagged representative `⟨k.succPNat, σ⟩`.

## Refined strata and counts

- `HasWeilSwan K Ω σ s` holds if some natural Artin exponent `a` for
  `σ` satisfies `a - (k + 1) = s`. Subtraction in `ℕ` implements
  Henniart's formula `max(0, a - n)` in §1.2 and takes the unramified
  rank-one class of Artin exponent zero to Swan exponent zero.
- `weilTorsionNumber K Ω σ` is the `Nat.card` of the subtype of
  `z : ℂˣ` for which the unramified twist fixes `σ`. This implements
  the orbit stabilizer cardinality from the route note, §2.2.
  `Nat.card` gives zero if the subtype is infinite.
- `weilRefinedStratum K Ω k s f` is `W_K(k+1,s,f)` of the route note,
  §2.2. It consists of the twist orbits containing a rank `k + 1`
  class with Swan exponent `s` and torsion number `f`.
- `weilTwistIrreducibleCount K Ω k s` is `T_K(k+1,s)` of the route
  note, §2.2, the `Set.encard` of the refined stratum at `f = 1`.
  It has type `ℕ∞`, with `⊤` for an infinite stratum.
- `weilConductorCount K Ω k j` is `C_K(n,j)` for `n = k + 1`,
  as in Henniart 1988, §1.3, with the range of the route note, §2.3
  and its Remark `rem:range`. It sums `T_K(d,s)` over positive divisors
  `d` of `n` and natural `s` with `n * s ≤ d * j`. The outer index
  uses `n.divisors`, and the inner `Finset.range (d * j / n + 1)`
  includes `s = 0`. A positive divisor `d` has rank parameter `d - 1`.

## P-adic specialization

For `F : PadicField p`, take `K = F.Carrier` and
`Ω = AlgebraicClosure F.Carrier`, with the valuative relation, topology and
local-field instance from `F.canonicalTopologicalData`. The characteristic-zero
instance from the `Padic p` algebra gives the separable-closure instance.
The p-adic Weil representation abbreviations in `Weil.Local.Parameters`
already use this Weil group by unfolding `Weil.Local.localWeilGroup`.
They retain their original rank argument, including rank zero for
`LocalContinuousIrreducibleWeilClasses`.

| `Langlands.Henniart.LocalNumerical` | Corresponding p-adic declaration |
| --- | --- |
| `IrreducibleWeilClass K Ω n` | `Langlands.Correspondence.IrreducibleWeilClass F n` |
| `weilClassForget K Ω σ` | `Langlands.Correspondence.weilClassForget F σ` |
| `HasArtinConductor K Ω σ a` | `Langlands.Henniart.Numerical.HasArtinConductor F σ a` |
| `weilUnramifiedTwist K Ω k z` | `Langlands.Henniart.Numerical.weilUnramifiedTwist F k z` |
| `weilOrbitStratum K Ω k a` | `Langlands.Henniart.Numerical.weilOrbitStratum F k a` |
| `HasWeilSwan K Ω σ s` | `Langlands.Henniart.Numerical.HasWeilSwan F σ s` |
| `weilTorsionNumber K Ω σ` | `Langlands.Henniart.Numerical.weilTorsionNumber F σ` |
| `weilRefinedStratum K Ω k s f` | `Langlands.Henniart.Numerical.weilRefinedStratum F k s f` |
| `weilTwistIrreducibleCount K Ω k s` | `Langlands.Henniart.Numerical.weilTwistIrreducibleCount F k s` |
| `weilConductorCount K Ω k j` | `Langlands.Henniart.Numerical.weilConductorCount F k j` |

The class and forget map specialize by unfolding.

```lean
import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.Correspondence.Domains

noncomputable section
open Langlands Langlands.Henniart Langlands.Correspondence
universe uK uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

example (n : ℕ+) : IrreducibleWeilClass.{uK, uW} F n =
    LocalNumerical.IrreducibleWeilClass.{uK, uK, uW}
      F.Carrier (AlgebraicClosure F.Carrier) n := rfl

example {n : ℕ+} (σ : IrreducibleWeilClass.{uK, uW} F n) :
    weilClassForget F σ =
      LocalNumerical.weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ := rfl
```

## Laurent-series specialization

The example installs `Langlands.LocalField.Laurent.valuativeRel 𝓀`
locally. Inference supplies Mathlib's X-adic topology on `LaurentSeries 𝓀`,
`Langlands.LocalField.Laurent.localField` from `Field 𝓀` and `Finite 𝓀`, and
Mathlib's algebra and separable-closure instances for `SeparableClosure`.

```lean
import Langlands.Correspondence.HenniartLocalNumerical
import Langlands.LocalField.LaurentSeries

noncomputable section
open Langlands Langlands.Henniart
universe u uW

attribute [local instance] LocalField.Laurent.valuativeRel

example (𝓀 : Type u) [Field 𝓀] [Finite 𝓀] (k s : ℕ) : ℕ∞ :=
  LocalNumerical.weilTwistIrreducibleCount.{u, u, uW}
    (LaurentSeries 𝓀) (SeparableClosure (LaurentSeries 𝓀)) k s
```

## Sources

- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544. Registered
  `henniart-1988-numerical`, SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  Sections 1.1–1.3, printed pp. 497–498 (PDF pp. 2–3), specify the classes,
  the geometric twist, the conductor conventions and the divisor sum.
- Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
  GTM 67 (1979). Registered `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  Chapter VI §2, Proposition 2 and Corollary 1′, printed pp. 100–101
  (PDF pp. 107–108), give the finite ramification sum used in the Artin
  predicate.
- Operator route note, *The numerical local Langlands correspondence for
  GL_n*, 16 November 2026. Registered
  `operator-numerical-llc-route-2026-11-16`, directory SHA-256
  `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
  `numerical-LLC-route.tex`, §§2.1–2.3, gives the orbit strata, torsion
  number and counts. Remark `rem:range` reconciles the zero Swan term
  with the rank-one and tame cases of Henniart 1988, §§3.1–3.2.
