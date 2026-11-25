/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Basic consequences of properness

Source:
literature/blueprint/master/blueprint/sec-abelian-varieties/cor-pqf-proper-quasifinite-finite/
pqf-lem-proper-basic.md, node pqf-lem-proper-basic, order 528 (blueprint: pqf-lem-proper-basic).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-- A proper morphism is separated, universally closed, of finite type, quasi-compact,
and quasi-separated. Over an affine base, its source is separated and quasi-compact.
Source: blueprint node pqf-lem-proper-basic, order 528 (blueprint: pqf-lem-proper-basic).
Proof: By [def-weil-proper-morphism], unpack properness to obtain separatedness,
universal closedness, and finite type. Finite type means locally of finite type together
with quasi-compactness [def-weil-finite-type-morphism]; these are the third and fourth
conjuncts. Separatedness implies quasi-separatedness [lem-pc-separated-quasi-separated],
so the diagonal is quasi-compact. If the base is affine, it is quasi-compact; applying
quasi-compactness of `f` to the whole base gives quasi-compactness of `X`. Finally,
separatedness of `f` over the affine base gives separatedness of `X`
[lem-sc-separated-over-affine-scheme-separated].
-/
theorem AlgebraicGeometry.proper_basic
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      QuasiSeparated f ∧ (IsAffine S → X.IsSeparated ∧ CompactSpace X) := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro hS
  let : IsAffine S := hS
  refine ⟨?_, QuasiCompact.compactSpace_of_compactSpace f⟩
  exact HasAffineProperty.iff_of_isAffine.mp (inferInstance : IsSeparated f)
