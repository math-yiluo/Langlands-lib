module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The Jacobi-Zariski sequence and the sequence of differentials of a tower

Let `A → B → C` be ring maps, let `α : A[x_s, s ∈ S] → B` be a presentation with kernel `I`, let
`β : B[y_t, t ∈ T] → C` be a presentation with kernel `J`, and let `γ : A[x_s, y_t] → C` be the
induced presentation of `C` with kernel `K`. The naive cotangent complexes of the three
presentations give the Jacobi-Zariski exact sequence of `C`-modules
```
H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0.
```
Exactness at the four right hand nodes is `Algebra.H1Cotangent.exact_map_δ`,
`Algebra.H1Cotangent.exact_δ_mapBaseChange`, `KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.map_surjective`. This file proves exactness at `H₁(L_{C/A})`: inside `K/K²`,
the image of `H₁(NL_{B/A} ⊗_B C) = Ker(I/I² ⊗_B C → Ω_{A[x_s]/A} ⊗ C)` under the map
`I/I² ⊗_B C → K/K²` induced by `A[x_s] → A[x_s, y_t]` is the intersection of
`H₁(L_{C/A}) = Ker(K/K² → Ω_{A[x_s, y_t]/A} ⊗ C)` with the kernel of the map `K/K² → J/J²`
induced by `A[x_s, y_t] → B[y_t]`. It also shows that `C ⊗_B Ω_{B/A} → Ω_{C/A}` is injective
when `H₁(L_{C/B}) = 0`, for instance when `B → C` is smooth.

## Main results

* `Algebra.Generators.Cotangent.map_ker_baseChange_cotangentComplex`: the Jacobi-Zariski sequence
  is exact at `H₁(L_{C/A})`, as an equality of `C`-submodules of `K/K²`.
* `KaehlerDifferential.mapBaseChange_injective`: if `H₁(L_{B/A}) = 0`, then
  `KaehlerDifferential.mapBaseChange R A B : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]` is injective, so that
  `0 → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` is exact.

## Implementation notes

The presentations `α`, `β` and `γ` are `P : Algebra.Generators R S σ`,
`Q : Algebra.Generators S T ι` and `Q.comp P`, so `P.toExtension.Cotangent`,
`(Q.comp P).toExtension.Cotangent` and `Q.toExtension.Cotangent` are `I/I²`, `K/K²` and `J/J²`.
Exactness at `H₁(L_{C/A})` is recorded as an equality of submodules of `K/K²` rather than as a
`Function.Exact`.

In `KaehlerDifferential.mapBaseChange_injective` the tower is written `R → A → B`, matching
`KaehlerDifferential.mapBaseChange`, and the hypothesis is
`Subsingleton (Algebra.H1Cotangent A B)`, which holds by instance inference when `A → B` is smooth
or formally smooth.

## References

* [StacksProject 00S2](https://stacks.math.columbia.edu/tag/00S2)
* [StacksProject 04B2](https://stacks.math.columbia.edu/tag/04B2)
* [StacksProject 00RS](https://stacks.math.columbia.edu/tag/00RS)
-/

@[expose] public section

universe w₁ w₂ u₁ u₂ u₃

-- `Generators.{w, u₁, u₂}` depends on three universe variables and to improve performance
-- of universe unification, it should hold that `w > u₁` and `w > u₂` in the lexicographic
-- order.

namespace Stacks.KaehlerDifferential.JacobiZariski

open Algebra

end Stacks.KaehlerDifferential.JacobiZariski

@[expose] public section

namespace Algebra.Generators.Cotangent

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {σ : Type w₂}

end Algebra.Generators.Cotangent

end

@[expose] public section

/-- **The sequence of differentials of a tower is exact on the left**: let `R → A → B` be ring
maps such that `H₁(L_{B/A}) = 0`, for instance with `A → B` smooth. Then the canonical map
`B ⊗_A Ω_{A/R} → Ω_{B/R}` is injective, so that `0 → B ⊗_A Ω_{A/R} → Ω_{B/R} → Ω_{B/A} → 0` is
a short exact sequence. -/
@[stacks 04B2 "Exactness at `C ⊗_B Ω_{B/A}`, the one node of the sequence that is not already
in Mathlib; the other two are `KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.map_surjective`. Stated under `H₁(L_{C/B}) = 0`, the hypothesis the
source's second proof uses, which the tag's smoothness gives by instance inference. See the
module docstring."]
public theorem KaehlerDifferential.mapBaseChange_injective (R : Type*) [CommRing R]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Subsingleton (Algebra.H1Cotangent A B)] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
  (LinearMap.injective_iff_eq_zero_of_exact
    (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B)).mpr (Subsingleton.elim _ _)

namespace Stacks.KaehlerDifferential.LeftExactness

end Stacks.KaehlerDifferential.LeftExactness

end
