/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Abelian varieties

Following Mathlib, a group scheme over a field `K` is an object `A` of `Over (Spec (.of K))`
equipped with `CategoryTheory.GrpObj A`. An *abelian variety* is such an `A` whose structure
morphism is proper and smooth and whose underlying space is connected.

The group structure is deliberately **not** a parameter of `AlgebraicGeometry.IsAbelianVariety`:
were it one, `IsAbelianVariety A` would be a different proposition for each `GrpObj A` instance
in scope. A declaration about abelian varieties therefore takes `[GrpObj A] [IsAbelianVariety A]`
side by side.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety`: proper, smooth and connected over `K`.
- `AlgebraicGeometry.IsAbelianVariety.dim`: the dimension of an abelian variety.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.topologicalKrullDim_eq`: the Krull dimension of an abelian
  variety is the natural number `IsAbelianVariety.dim`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `definition-abelian-variety`: Abelian varieties.

An *abelian variety* over a field `K` is a group scheme over `K` which is proper, smooth and
connected; its *dimension* is `AlgebraicGeometry.IsAbelianVariety.dim`, the Krull dimension of
its underlying space.

This is also blueprint `definition-abelian-variety--1`. As blueprint
`lemma-abelian-variety-commutative--1` records, that these are exactly the complete group varieties
is `AlgebraicGeometry.IsAbelianVariety.geometricallyIntegral` (blueprint
`lemma-abelian-variety-commutative--1`). -/
class IsAbelianVariety (A : Over (Spec (.of K))) : Prop
    extends IsProper A.hom, Smooth A.hom, ConnectedSpace A.left

/-- Blueprint `theorem-picard-scheme-jacobian-over-separably--3`: the dimension of an abelian
variety, that is, the Krull dimension of its underlying topological space, as a natural number.

`AlgebraicGeometry.IsAbelianVariety.topologicalKrullDim_eq` says that this really is the Krull
dimension: an abelian variety is nonempty and finite-dimensional. -/
noncomputable def IsAbelianVariety.dim (A : Over (Spec (.of K))) [IsAbelianVariety A] : ℕ :=
  ((topologicalKrullDim A.left).unbotD 0).toNat

/-- The Krull dimension of an abelian variety is the natural number
`AlgebraicGeometry.IsAbelianVariety.dim`: it is neither `⊥` (the variety is nonempty, being
connected) nor `⊤` (it is quasi-compact and of finite type over `K`). -/
theorem IsAbelianVariety.topologicalKrullDim_eq (A : Over (Spec (.of K))) [IsAbelianVariety A] :
    topologicalKrullDim A.left = (IsAbelianVariety.dim A : ℕ∞) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hne := topologicalKrullDim_ne_top_of_compactSpace A.hom
  obtain ⟨x⟩ := (inferInstance : Nonempty A.left)
  have : Nonempty (TopologicalSpace.IrreducibleCloseds A.left) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim A.left ≠ ⊥ :=
    ne_bot_of_le_ne_bot WithBot.coe_ne_bot Order.krullDim_nonneg
  rw [IsAbelianVariety.dim]
  generalize topologicalKrullDim A.left = d at hne hbot ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe d => induction d using ENat.recTopCoe <;> simp_all

end AlgebraicGeometry
