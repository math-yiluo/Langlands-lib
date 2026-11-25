/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sets.CompactOpenCovered
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

@[expose] public section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

variable (𝒰 : Scheme.Cover.{v} (precoverage P) S)

namespace Scheme.Cover.QuasiCompact

variable {𝒰 : Cover.{v} (Scheme.precoverage P) S}

open TopologicalSpace.Opens

open TopologicalSpace _root_.AlgebraicGeometry.Scheme.Opens _root_.TopologicalSpace.Opens


lemma exists_hom [P.IsMultiplicative] {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P))
    [P.RespectsLeft @IsOpenImmersion] [CompactSpace S] [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    ∃ (𝒱 : Scheme.AffineCover.{w} P S) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : Opens S).carrier from isCompact_univ)
  simp only [coe_top, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_iUnion,
    Set.mem_image, SetLike.mem_coe, forall_const] at h
  choose idx x hmem hx using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { I₀ := ULift (Fin n)
        X i := Γ(_, V i.down)
        f i := (hV _).fromSpec ≫ 𝒰.f (f _)
        idx s := ⟨idx s⟩
        covers s := by
          use (hV _).isoSpec.hom.base ⟨x s, hmem s⟩
          rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
            Iso.hom_inv_id_assoc]
          simp [hx]
        map_prop i :=
          RespectsLeft.precomp (Q := IsOpenImmersion) _ inferInstance _ (𝒰.map_prop _) }
  · exact
      { s₀ i := f i.down
        h₀ i := (hV i.down).fromSpec }
  · infer_instance
  · infer_instance


end AlgebraicGeometry.Scheme.Cover.QuasiCompact
