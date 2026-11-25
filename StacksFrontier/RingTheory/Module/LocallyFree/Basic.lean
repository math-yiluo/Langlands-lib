module

public import Mathlib.Tactic.CrossRefAttribute
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
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A finite flat module that is not projective

Let `R = C^∞(ℝ)` be the ring of smooth functions `ℝ → ℝ` and let `I` be the ideal of those
`f ∈ R` which vanish identically on some open neighborhood `(-ε, ε)` of `0`. The quotient
`M = R / I` is a finite and flat `R`-module which is not projective, so "finite and flat implies
projective" fails over a general commutative ring. In contrast, over local rings finite
projectivity of a finite module descends along a flat local homomorphism.

## Main definitions

* `Stacks.FiniteFlatNotProjective.smoothSubring`: the ring `C^∞(ℝ)`, as a subring of `ℝ → ℝ`.
* `Stacks.FiniteFlatNotProjective.vanishNearZero`: the ideal `I`.
* `Stacks.FiniteFlatNotProjective.QuotientModule`: the module `M = R / I`.

## Main results

* `Stacks.FiniteFlatNotProjective.quotientModule_flat`: `M` is a flat `R`-module.
* `Stacks.FiniteFlatNotProjective.quotientModule_not_projective`: `M` is not a projective
  `R`-module.
* `Stacks.FiniteFlatNotProjective.quotientModule_isLocalization`: `M` is the localization `R_m`
  of `R` at the maximal ideal `m` of functions vanishing at `0`.
* `Stacks.FiniteFlatNotProjective.quotientModule_isLocalization_finite_flat_not_projective`:
  Remark 00NY, all of the above together with finiteness of `M`.
* `finite_projective_iff_baseChange`: for a flat local homomorphism `R → S` of local rings and a
  finite `R`-module `M`, `M` is finite projective over `R` if and only if `S ⊗[R] M` is finite
  projective over `S`.
-/

@[expose] public section

open scoped Topology

namespace Stacks.FiniteFlatNotProjective

/-! ### Basic API -/

/-! ### Flatness -/

/-! ### Non-projectivity -/

/-! ### `R/I` is the localization `R_m` -/

end Stacks.FiniteFlatNotProjective

/-! ### Finite projectivity along a flat local homomorphism -/

@[expose] public section

open scoped TensorProduct

/-- Let `R → S` be a flat local homomorphism of local rings and let `M` be a finite `R`-module.
Then `M` is projective over `R` if and only if `S ⊗[R] M` is projective over `S`. -/
theorem projective_iff_baseChange {R : Type*} {S : Type*} {M : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)]
    [Module.Flat R S]
    [Module.Finite R M] :
    Module.Projective R M ↔ Module.Projective S (S ⊗[R] M) := by
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  refine ⟨fun _ ↦ .tensorProduct, fun _ ↦ ?_⟩
  have : Module.Flat R M := (Module.Flat.iff_flat_tensorProduct R M S).mp .of_projective
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  exact .of_free
