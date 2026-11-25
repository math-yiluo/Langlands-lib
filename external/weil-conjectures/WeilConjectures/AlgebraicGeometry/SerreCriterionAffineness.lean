/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealH1Representatives
import WeilConjectures.AlgebraicGeometry.QuasiCompactH1Zero

/-!
# Serre's criterion for affineness

Source: Stacks Project, Cohomology of Schemes, Lemma 30.3.2, Tag 01XG
(blueprint: pqf-lem-serre-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact, quasi-separated scheme is affine if the first cohomology of every
quasi-coherent ideal sheaf of finite type vanishes. Quasi-coherent ideal sheaves are
`X.IdealSheafData`, and `I.toModules` is their associated submodule of `𝒪_X`.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.3.2, Tag 01XG
(blueprint: pqf-lem-serre-criterion).

Proof:
1. By `lemma-nagata-ideal-directed-union-finite-type` (Stacks Tag 01PG), every
quasi-coherent ideal on a quasi-compact, quasi-separated scheme is the directed union
of its quasi-coherent subideals of finite type. This union is their colimit as modules.
Affine opens form a quasi-compact basis, and quasi-separatedness makes intersections
of quasi-compact opens quasi-compact. Thus
`lem-weil-pbc-qs-scheme-cohomology-directed-colimit`, with `U = X` and `q = 1`, applies.
Every first cohomology class comes from a finite-type subideal, where the hypothesis
makes it zero. Hence first cohomology vanishes for all quasi-coherent ideals.
2. Apply `lem-pqf-quasicompact-h1-zero` (Stacks Tag 01XF): quasi-compactness and this
vanishing for all quasi-coherent ideals imply that the scheme is affine. -/
theorem isAffine_of_finiteType_ideal_h1_zero (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ I : X.IdealSheafData, I.toModules.IsFiniteType →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X := by
  apply AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero X
  intro I hI
  have hzero : ∀ x : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules,
      x = 0 := by
    intro x
    obtain ⟨K, _, hK, f, y, _, hy⟩ := ideal_h1_finiteType_representative X I hI x
    have := ModuleCat.subsingleton_of_isZero (h K hK)
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

end AlgebraicGeometry.Scheme
