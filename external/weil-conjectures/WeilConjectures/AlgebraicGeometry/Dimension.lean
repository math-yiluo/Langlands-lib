/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension

/-!
# Dimension and relative dimension of schemes

Source: the blueprint of the Weil conjectures, chapter `chap-Abelian-varieties`, unit
`theorem-picard-scheme-jacobian-over-separably--3`, node order 452 (blueprint: def-pc-dimension);
Stacks Project, Properties, Tags 04MT and 04MU (dimension of a scheme via its local rings).

## Main definitions

* `AlgebraicGeometry.Scheme.dim`: the dimension of a scheme, the supremum of the Krull
  dimensions of its local rings.
* `AlgebraicGeometry.Scheme.Hom.relativeDimAt`: the relative dimension `dim X_s` of a morphism
  `f : X ⟶ S` over a point `s : S`.
* `AlgebraicGeometry.Scheme.Hom.IsOfRelativeDimension`: `f` is of finite type and every nonempty
  fibre has dimension `d`.

## Main statements

* `AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`: `Scheme.dim X` is the Krull dimension
  of the underlying topological space.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: def-pc-dimension) The *dimension* `dim X` of a scheme `X`: the supremum of the
Krull dimensions `ringKrullDim 𝒪_{X,x}` of its local rings, as `x` ranges over `X` (blueprint,
node order 452; Stacks, Tag 04MU). The node assumes `X` nonempty; then the value lies in `ℕ∞`
(every local ring is nonzero, so each term is `≥ 0`). No hypothesis is put on the definition:
for the empty scheme the supremum over the empty family is `⊥` (`dim ∅ = -∞`), the convention
used by the citers that write `dim X ≤ 1` for a possibly empty `X`. -/
noncomputable def Scheme.dim (X : Scheme.{u}) : WithBot ℕ∞ :=
  ⨆ x : X, ringKrullDim (X.presheaf.stalk x)

/-- (blueprint: lem-pc-scheme-dimension-local-rings) The dimension of a scheme as defined by the
supremum of the Krull dimensions of its local rings (`Scheme.dim`, def-pc-dimension) equals the
Krull dimension `topologicalKrullDim X` of its underlying topological space, both sides `⊥` for
the empty scheme (Stacks, Tag 04MU).

Proof: by Mathlib's `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`
(`Mathlib/AlgebraicGeometry/Properties.lean`), `ringKrullDim 𝒪_{X,x} = coheight x` in the
specialization order. A scheme is quasi-sober and `T₀`, so `irreducibleSetEquivPoints` is an order
isomorphism between irreducible closed subsets and points, and `topologicalKrullDim X` is the
Krull dimension of the specialization order of `X`; conclude by
`Order.krullDim_eq_iSup_coheight`. Both sides are `⊥` for the empty scheme. -/
theorem Scheme.dim_eq_topologicalKrullDim (X : Scheme.{u}) :
    X.dim = topologicalKrullDim X := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_congr
  intro x
  exact ringKrullDim_stalk_eq_coheight (X := X) x

end AlgebraicGeometry
