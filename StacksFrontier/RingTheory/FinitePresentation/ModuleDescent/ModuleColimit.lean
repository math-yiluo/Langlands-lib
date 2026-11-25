module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
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
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Colimits and maps of finite presentation: the module colimit condition

Let `A` be a commutative ring and `M, N` be `A`-modules. Suppose
`R = colim_{i ∈ I} R_i` is a directed colimit of `A`-algebras, where `(I, ≤)`
is a directed poset and `i ↦ R_i` is a functor to `A`-algebras with transition
maps `φ_{ij} : R_i → R_j` for `i ≤ j` and canonical maps `φ_i : R_i → R`.

The key tool is that tensoring a fixed `A`-module `P` with the family commutes
with directed colimits:  `P ⊗_A R = colim_i (P ⊗_A R_i)` as `R`-modules. This file sets up
the directed system, the canonical maps `R_i ⊗_A P → R ⊗_A P` and the statement
`IsModuleColimit` of this colimit property.

## Main results

* `statement_one`: if `M` is finite and `u, u' : M → N` agree after base change to `R`,
  they already agree after base change to some `R_i`.
* `baseChange_surjective_iff_coker_subsingleton`: a base change of `u : M → N` is surjective
  iff the base change of its cokernel vanishes.

## Conventions

All rings are commutative with unit; all algebra maps are unital `A`-algebra
homomorphisms.  We use Mathlib's base change `S ⊗[A] M` (the algebra on the left), which
is canonically isomorphic to `M ⊗_A S`.
-/

@[expose] public section

universe u v

@[expose] public section

open scoped TensorProduct

namespace Stacks.FinitePresentation.ColimitDescent

section Setup

variable {A : Type*} [CommRing A]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]

/-- The canonical `A`-linear map `R_i ⊗_A P → S ⊗_A P` induced by the algebra
map `ψ i : R_i → S` (i.e. `(ψ i) ⊗ id_P`). -/
noncomputable def canonMod (ψ : ∀ i, R i →ₐ[A] S)
    (P : Type*) [AddCommGroup P] [Module A P] (i : ι) :
    (R i) ⊗[A] P →ₗ[A] S ⊗[A] P :=
  TensorProduct.map (ψ i).toLinearMap LinearMap.id

/-- The transition `A`-linear map `R_i ⊗_A P → R_j ⊗_A P` induced by
`φ_{ij} : R_i → R_j` (i.e. `φ_{ij} ⊗ id_P`). -/
noncomputable def transMod (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (P : Type*) [AddCommGroup P] [Module A P] ⦃i j : ι⦄ (hij : i ≤ j) :
    (R i) ⊗[A] P →ₗ[A] (R j) ⊗[A] P :=
  TensorProduct.map (φ hij).toLinearMap LinearMap.id

section MovedHelpers

variable {P : Type*} [AddCommGroup P] [Module A P]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

omit [Preorder ι] in
omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `canonMod ψ P i` sends `r ⊗ p` to `ψ i r ⊗ p`. -/
@[simp] lemma canonMod_tmul (ψ : ∀ i, R i →ₐ[A] S) (i : ι) (r : R i) (p : P) :
    canonMod ψ P i (r ⊗ₜ[A] p) = (ψ i r) ⊗ₜ[A] p := rfl

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `transMod φ P hij` sends `r ⊗ p` to `φ hij r ⊗ p`. -/
@[simp] lemma transMod_tmul (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    ⦃i j : ι⦄ (hij : i ≤ j) (r : R i) (p : P) :
    transMod φ P hij (r ⊗ₜ[A] p) = (φ hij r) ⊗ₜ[A] p := rfl

end MovedHelpers

/-- The statement that `S ⊗_A P = colim_i (R_i ⊗_A P)`: the canonical maps
`canonMod` are jointly surjective, and two
elements of `R_i ⊗_A P` have the same image in `S ⊗_A P` iff they agree in
`R_j ⊗_A P` for some `j ≥ i`.  This is the conclusion of "tensor product
commutes with directed colimits" applied to the module `P`. -/
structure IsModuleColimit (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
    (ψ : ∀ i, R i →ₐ[A] S)
    (P : Type*) [AddCommGroup P] [Module A P] : Prop where
  /-- Joint surjectivity: every element of `S ⊗_A P` comes from some `R_i ⊗_A P`. -/
  jointly_surjective : ∀ x : S ⊗[A] P, ∃ (i : ι) (y : (R i) ⊗[A] P),
    canonMod ψ P i y = x
  /-- Equalizer condition: elements of `R_i ⊗_A P` mapping to the same element of
  `S ⊗_A P` already agree in `R_j ⊗_A P` for some `j ≥ i`. -/
  exists_eq_of_canonMod_eq : ∀ (i : ι) (y z : (R i) ⊗[A] P),
    canonMod ψ P i y = canonMod ψ P i z →
    ∃ (j : ι) (hij : i ≤ j), transMod φ P hij y = transMod φ P hij z

end Setup

section Statements

variable {A : Type*} [CommRing A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]
variable (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
variable (ψ : ∀ i, R i →ₐ[A] S)

end Statements

end Stacks.FinitePresentation.ColimitDescent
