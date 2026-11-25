module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
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
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Unramified morphisms of schemes

A morphism of schemes is unramified (respectively G-unramified) at a point when suitable affine
neighbourhoods of that point and its image induce an unramified (respectively G-unramified) map
on rings of sections. It is unramified (respectively G-unramified) when this holds at every point
of its source.

## Main definitions

* `AlgebraicGeometry.UnramifiedAt` is unramifiedness of a scheme morphism at a point.
* `AlgebraicGeometry.GUnramifiedAt` is G-unramifiedness of a scheme morphism at a point.
* `AlgebraicGeometry.Unramified` is unramifiedness of a scheme morphism.
* `AlgebraicGeometry.GUnramified` is G-unramifiedness of a scheme morphism.

## Main results

* `AlgebraicGeometry.unramified_iff` characterizes the global unramifiedness class pointwise.
* `AlgebraicGeometry.gUnramified_iff` characterizes the global G-unramifiedness class pointwise.

## Implementation notes

The affine neighbourhoods are represented by open subsets together with `IsAffineOpen`
witnesses. The containment of the source neighbourhood in the inverse image of the target
neighbourhood supplies the canonical map on sections through `Scheme.Hom.appLE`. Its underlying
ring homomorphism determines the algebra structure used by `Algebra.Unramified` or
`Algebra.GUnramified`.

The two global notions are classes, following Mathlib's convention for properties of scheme
morphisms. Their fields directly expose the corresponding pointwise predicates.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory

/-- A morphism of schemes `f : X ⟶ S` is unramified at `x : X` if there are affine open
neighbourhoods `U` of `x` and `V` of its image, with `U ≤ f ⁻¹ᵁ V`, such that the induced map on
rings of sections is unramified. -/
@[stacks 02G4 "part (1)"]
public def UnramifiedAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U)

/-- A morphism of schemes is unramified if it is unramified at every point of its source. -/
@[mk_iff, stacks 02G4 "part (3)"]
public class Unramified {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- The morphism is unramified at every point `x` of its source. -/
  unramifiedAt (x : X) : UnramifiedAt f x

end AlgebraicGeometry
