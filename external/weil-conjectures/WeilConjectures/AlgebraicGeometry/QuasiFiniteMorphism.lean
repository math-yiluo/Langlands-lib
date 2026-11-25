/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime

/-!
# Quasi-finite morphisms in the Stacks sense

Source: Stacks Project, Morphisms of Schemes, Tag 01TD
(blueprint: pqf-def-quasifinite), and the blueprint's finite-fibres convention.

Mathlib's `LocallyQuasiFinite` and `Scheme.Hom.QuasiFiniteAt` do not impose local finite
type. The predicates here include the finite-type conditions of Tag 01TD; with these conditions
added they agree with Mathlib's notions (`Scheme.Hom.isQuasiFiniteAtPoint_iff_quasiFiniteAt`,
`Scheme.Hom.isLocallyQuasiFinite_iff`, `Scheme.Hom.isQuasiFinite_iff`). The ring-level
notion "of finite type and quasi-finite at a prime" (Stacks Tag 00PL) is the project's
`Algebra.IsQuasiFiniteAtPrime` (blueprint: def-weil-pbc-ring-map-quasi-finite-at-prime).
The scheme-theoretic fibre is the existing `Scheme.Hom.fiber`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Quasi-finite at a point in the sense of Stacks Tag 01TD
(blueprint: pqf-def-quasifinite): some affine neighbourhood `U` of `x` maps into an affine
open `V`, and the ring map `Γ(S, V) → Γ(X, U)` is of finite type and quasi-finite at the
prime corresponding to `x`, in the sense of `Algebra.IsQuasiFiniteAtPrime`
(Stacks Tag 00PL, blueprint: def-weil-pbc-ring-map-quasi-finite-at-prime). For `f` locally
of finite type it is Mathlib's `f.QuasiFiniteAt x`
(`Scheme.Hom.isQuasiFiniteAtPoint_iff_quasiFiniteAt`). -/
def IsQuasiFiniteAtPoint {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : X.Opens) (hx : x ∈ U) (hU : AlgebraicGeometry.IsAffineOpen U)
    (V : S.Opens) (_ : AlgebraicGeometry.IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
    letI := (f.appLE V U e).hom.toAlgebra
    ∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U),
      letI := hft
      Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)

/-- Locally quasi-finite in the sense of Stacks Tag 01TD
(blueprint: pqf-def-quasifinite): quasi-finite at every point, including the local
finite-type requirement in `IsQuasiFiniteAtPoint`. It is equivalent to Mathlib's
`LocallyQuasiFinite f ∧ LocallyOfFiniteType f` (`Scheme.Hom.isLocallyQuasiFinite_iff`). -/
def IsLocallyQuasiFinite {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, IsQuasiFiniteAtPoint f x

/-- Quasi-finite in the sense of Stacks Tag 01TD (blueprint: pqf-def-quasifinite):
of finite type, with every point isolated in its fibre. Finite type is expressed as
locally of finite type and quasi-compact. The singleton is open in the scheme-theoretic
fibre, which is canonically homeomorphic to the set-theoretic fibre. It is equivalent to
Mathlib's `LocallyQuasiFinite f ∧ LocallyOfFiniteType f ∧ QuasiCompact f`
(`Scheme.Hom.isQuasiFinite_iff`). -/
def IsQuasiFinite {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) : Prop :=
  AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f ∧
    ∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x)))

/-- Finite fibres as in the blueprint's convention appended to Stacks Tag 01TD
(blueprint: pqf-def-quasifinite): the inverse image of every singleton is finite. -/
def HasFiniteFibres {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S, (f ⁻¹' {s}).Finite

end AlgebraicGeometry.Scheme.Hom
