/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus

/-! # Openness of the fibre Cohen-Macaulay locus over a base open

Source: Stacks Project, Tag 045U.
(blueprint: lem-sbc-restricted-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)

private theorem fibre_depth_eq_ringKrullDim_restrict_iff
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens) (x : (f ⁻¹ᵁ U).toScheme) :
    ((IsLocalRing.depth
        (R := ((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x))
        (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x)) :
          WithBot ℕ∞) =
      ringKrullDim (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk
        ((f ∣_ U).asFiber x))) ↔
    ((IsLocalRing.depth (R := (f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1))
        ((f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1)) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1))) := by
  let tU : U.toScheme := (f ∣_ U) x
  let q := Limits.pullback.map (f ∣_ U) (U.toScheme.fromSpecResidueField tU) f
    (T.fromSpecResidueField (U.ι tU)) (f ⁻¹ᵁ U).ι
    (Spec.map (U.ι.residueFieldMap tU)) U.ι (by simp)
    (by exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι tU).symm)
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f U).flip tU
  have : IsIso q := hsq.isIso_fst_of_isIso
  have hbase : U.ι tU = f x.1 := morphismRestrict_base_coe f U x
  let q' : (f ∣_ U).fiber ((f ∣_ U) x) ⟶ f.fiber (f x.1) :=
    q ≫ eqToHom (congrArg f.fiber hbase)
  have : IsIso q' := inferInstance
  have hpoint : q' ((f ∣_ U).asFiber x) = f.asFiber x.1 := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q' ≫ f.fiberι (f x.1) =
        (f ∣_ U).fiberι ((f ∣_ U) x) ≫ (f ⁻¹ᵁ U).ι := by
      dsimp [q']
      have heq (t t' : T) (h : t = t') :
          eqToHom (congrArg f.fiber h) ≫ f.fiberι t' = f.fiberι t := by
        subst t'
        simp
      rw [Category.assoc, heq _ _ hbase]
      simp [q, tU, Scheme.Hom.fiberι]
    rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply]
    simp
  let e := ((f.fiber (f x.1)).presheaf.stalkCongr (.of_eq hpoint.symm) ≪≫
    asIso (q'.stalkMap ((f ∣_ U).asFiber x))).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e, ← depth_eq_of_ringEquiv e]

/-- The Cohen-Macaulay fibre-stalk locus is open over a flat finitely presented restriction.

Source: Stacks Project, Tag 045U (1), (2), with Cohen-Macaulayness expressed by depth.
Proof: Form the base restriction `f ∣_ U`. For each point of its source, the
restriction pullback square and the residue-field isomorphism of the open immersion
identify its fibre with the original fibre. Their stalks are isomorphic as local
rings, preserving depth and Krull dimension. The restricted fibres are locally of
finite type over fields, hence locally Noetherian. For these rings equality of depth
and Krull dimension is exactly Cohen-Macaulayness. Tag 045U (1), (2) says that this
locus in the restricted source is open. The source restriction inclusion is an open
immersion, and its image is precisely the set displayed below. Its image is open in X.
For an empty U or X this set is empty, which is open.
(blueprint: lem-sbc-restricted-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim_over_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    IsOpen {y : X | f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by
  let W := {x : (f ⁻¹ᵁ U).toScheme |
    (IsLocalRing.depth
      (R := ((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x))
      (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x)) :
        WithBot ℕ∞) =
      ringKrullDim (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk
        ((f ∣_ U).asFiber x))}
  have hW : IsOpen W := isOpen_fibre_depth_eq_ringKrullDim (f ∣_ U)
  have himage : (f ⁻¹ᵁ U).ι '' W = {y : X | f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (fibre_depth_eq_ringKrullDim_restrict_iff f U x).mp hx⟩
    · rintro ⟨hy, hd⟩
      exact ⟨⟨y, hy⟩, (fibre_depth_eq_ringKrullDim_restrict_iff f U ⟨y, hy⟩).mpr hd,
        rfl⟩
  rw [← himage]
  exact (f ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap W hW

end AlgebraicGeometry
