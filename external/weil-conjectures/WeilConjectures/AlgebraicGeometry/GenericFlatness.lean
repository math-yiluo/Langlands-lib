/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.AlgebraicGeometry.AffineGenericFlatness

/-! # Generic flatness for finite type morphisms

Source: Stacks Project, Tag 052A.
(blueprint: lem-sbc-generic-flatness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem flat_restrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : S.Opens} (hVU : V ≤ U) [Flat (f ∣_ U)] : Flat (f ∣_ V) := by
  have h : Flat (f ∣_ U ∣_ U.ι ⁻¹ᵁ V) := inferInstance
  have h' := (MorphismProperty.arrow_mk_iso_iff @Flat
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h
  have heq : U.ι ''ᵁ U.ι ⁻¹ᵁ V = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVU hx⟩, hx, rfl⟩
  rwa [heq] at h'

private theorem exists_nonempty_open_flat_restrict_affine_base {X S : Scheme.{u}}
    [IsAffine S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ Flat (f ∣_ U) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have ha (i : 𝒰.I₀) :
      ∃ a : Γ(S, ⊤), a ≠ 0 ∧ Flat ((𝒰.f i ≫ f) ∣_ S.basicOpen a) := by
    have : IsAffine (𝒰.X i) := by
      dsimp [𝒰, Scheme.OpenCover.finiteSubcover]
      infer_instance
    exact exists_nonzero_flat_restrict_basicOpen (𝒰.f i ≫ f)
  choose a ha0 haFlat using ha
  let U : S.Opens := ⨅ i, S.basicOpen (a i)
  have hmem (i : 𝒰.I₀) : genericPoint S ∈ S.basicOpen (a i) := by
    apply ((genericPoint_spec S).mem_open_set_iff (S.basicOpen (a i)).isOpen).mpr
    rw [Set.univ_inter]
    by_contra hn
    apply ha0 i
    exact (basicOpen_eq_bot_iff (a i)).mp ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hn)
  have hU : (U : Set S).Nonempty := by
    refine ⟨genericPoint S, ?_⟩
    dsimp only [U]
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hmem
  refine ⟨U, hU, ?_⟩
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (𝒰.pullback₁ (f ⁻¹ᵁ U).ι)
  intro i
  have : Flat ((𝒰.f i ≫ f) ∣_ U) :=
    flat_restrict_of_le (𝒰.f i ≫ f) (iInf_le (fun i ↦ S.basicOpen (a i)) i)
  rw [morphismRestrict_comp] at this
  let e := CategoryTheory.Limits.pullbackSymmetry (f ⁻¹ᵁ U).ι (𝒰.f i) ≪≫
    pullbackRestrictIsoRestrict (𝒰.f i) (f ⁻¹ᵁ U)
  have heq : (𝒰.pullback₁ (f ⁻¹ᵁ U).ι).f i ≫ f ∣_ U =
      e.hom ≫ (𝒰.f i ∣_ f ⁻¹ᵁ U) ≫ f ∣_ U := by
    change CategoryTheory.Limits.pullback.fst (f ⁻¹ᵁ U).ι (𝒰.f i) ≫ f ∣_ U = _
    simp [e]
  rw [heq]
  infer_instance

/-- A finite type morphism to an integral scheme is flat over a nonempty open.

Source: Stacks Project, Tag 052A, with the structure sheaf as the finite type module.
Proof: choose a nonempty affine open of the integral base, with coordinate domain A.
Quasi-compactness gives a finite affine cover of its inverse image, with coordinate
rings B_i finite type over A. Generic freeness, in the version for a finite type
algebra over an arbitrary domain (Tag 051T), gives nonzero elements a_i of A such
that each localized algebra (B_i)_{a_i} is free, hence flat, over A_{a_i}.
Intersect the finitely many basic opens D(a_i). Each is nonempty and contains
the generic point of the integral base, so their intersection is nonempty.
Restrict the flat chart maps further to this intersection. Their source opens
cover the inverse image, and flatness is local on the source, so the restricted
morphism is flat. Finally use the canonical isomorphism between a restriction
of a restriction and the restriction to its image in the original base.
For an empty inverse image the intersection is the whole affine base and source
locality is vacuous. No Noetherian or finite-presentation hypothesis is used.

(blueprint: lem-sbc-generic-flatness) -/
theorem exists_nonempty_open_flat_restrict {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ Flat (f ∣_ U) := by
  classical
  let x : S := Classical.choice inferInstance
  let V : S.Opens := (S.affineCover.f (S.affineCover.idx x)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hxV : x ∈ V := S.affineCover.covers x
  have : IsAffine V.toScheme := hV
  have : Nonempty V.toScheme := ⟨⟨x, hxV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  obtain ⟨W, hW, hflat⟩ := exists_nonempty_open_flat_restrict_affine_base (f ∣_ V)
  refine ⟨V.ι ''ᵁ W, ?_, ?_⟩
  · exact hW.image V.ι
  · exact (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict f V W)).mp hflat

end AlgebraicGeometry
