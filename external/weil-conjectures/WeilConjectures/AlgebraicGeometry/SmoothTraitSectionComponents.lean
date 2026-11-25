/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.AlgebraicGeometry.ConnectedGenericFibreTrait
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Comparing two sections of a smooth family over a trait

Source: Stacks Project, Tag 055Q, last two paragraphs, using Tag 055J.
-/

@[expose] public section

universe u
open CategoryTheory Limits Topology IsLocalRing
namespace AlgebraicGeometry

/-- Two sections of a smooth family over a DVR which meet the same special-fibre
component also meet the same generic-fibre component.

Source: Stacks Project, Tag 055Q, last two paragraphs, using Tag 055J.
Proof: The total space is locally noetherian because the morphism is smooth over a
noetherian affine base. The special-fibre component C of the section point is open
in the fibre, so choose an ambient open O cutting it out. The special fibre F is
closed in the total space. The open U = O ∪ (P ∖ F) therefore meets F exactly in C.
Take the connected component W of U containing the special point of σ. It is open
because U is locally noetherian and hence locally connected. The preimage of C is
preconnected and contains that point, so it lies in W. Thus both special section
points lie in W. Both sections factor through W because every trait point specializes
to its closed point and W is open. This component is
flat over the trait and its special fibre is reduced, by smoothness. Tag 055J makes
its generic fibre connected: a separating idempotent on that fibre extends over
each affine open, since a minimal denominator which is a positive power of a
uniformizer would give a nonzero nilpotent in the reduced special fibre. The affine
extensions are unique by flatness and glue to an idempotent on the connected total
space, a contradiction. The images of both generic section points therefore lie in
one connected subset of the original generic fibre, proving the assertion.
(blueprint: lem-sbc-smooth-trait-section-components) -/
theorem Smooth.trait_sections_mem_same_generic_component {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {P : Scheme.{u}}
    (g : P ⟶ Spec (.of R)) [Smooth g] [QuasiCompact g] [QuasiSeparated g]
    (σ τ : Spec (.of R) ⟶ P) (hσ : σ ≫ g = 𝟙 _) (hτ : τ ≫ g = 𝟙 _)
    (hclosed : τ (closedPoint R) ∈
      connectedComponentIn (g ⁻¹' {closedPoint R}) (σ (closedPoint R))) :
    τ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈
      connectedComponentIn (g ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)})
        (σ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) := by
  let s : Spec (.of R) := closedPoint R
  let η : Spec (.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hsection (φ : Spec (.of R) ⟶ P) (hφ : φ ≫ g = 𝟙 _) (t : Spec (.of R)) :
      g (φ t) = t := by
    rw [← Scheme.Hom.comp_apply, hφ]
    rfl
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian g
  have hσs : σ s ∈ g ⁻¹' {s} := hsection σ hσ s
  obtain ⟨t, ht, hct⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := (⟨σ s, hσs⟩ : g ⁻¹' {s})))
  let O : P.Opens := ⟨t, ht⟩
  have hO : (O : Set P) ∩ g ⁻¹' {s} =
      connectedComponentIn (g ⁻¹' {s}) (σ s) := by
    rw [connectedComponentIn_eq_image hσs, ← hct, Set.image_preimage_eq_inter_range,
      Subtype.range_coe]
    rfl
  have hF : IsClosed (g ⁻¹' {s}) :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (inferInstanceAs (maximalIdeal R).IsMaximal)).preimage g.continuous
  let U : P.Opens := O ⊔ ⟨(g ⁻¹' {s})ᶜ, hF.isOpen_compl⟩
  have hCU : connectedComponentIn (g ⁻¹' {s}) (σ s) ⊆ (U : Set P) := by
    intro z hz
    exact Or.inl (hO.ge hz).1
  have hσC : σ s ∈ connectedComponentIn (g ⁻¹' {s}) (σ s) :=
    mem_connectedComponentIn (hsection σ hσ s)
  let σs : U := ⟨σ s, hCU hσC⟩
  let W : U.toScheme.Opens := ⟨connectedComponent σs, isOpen_connectedComponent⟩
  let j : W.toScheme ⟶ P := W.ι ≫ U.ι
  have hWC : connectedComponentIn (g ⁻¹' {s}) (σ s) ⊆ Set.range j := by
    have hconn : _root_.IsPreconnected (U.ι ⁻¹'
        connectedComponentIn (g ⁻¹' {s}) (σ s)) := by
      rw [← U.ι.isOpenEmbedding.isInducing.isPreconnected_image,
        Set.image_preimage_eq_of_subset]
      · exact isPreconnected_connectedComponentIn
      · simpa only [Scheme.Opens.range_ι] using hCU
    have hsub := hconn.subset_connectedComponent (x := σs) hσC
    intro z hz
    have hzU := hCU hz
    refine ⟨⟨⟨z, hzU⟩, hsub hz⟩, rfl⟩
  have hsections (φ : Spec (.of R) ⟶ P)
      (hφ : φ s ∈ connectedComponentIn (g ⁻¹' {s}) (σ s)) :
      Set.range φ ⊆ Set.range j := by
    rintro _ ⟨t, rfl⟩
    exact ((specializes_closedPoint t).map φ.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hWC hφ)
  let σW : Spec (.of R) ⟶ W.toScheme :=
    IsOpenImmersion.lift j σ (hsections σ hσC)
  let τW : Spec (.of R) ⟶ W.toScheme :=
    IsOpenImmersion.lift j τ (hsections τ hclosed)
  have hσW : σW ≫ j = σ := IsOpenImmersion.lift_fac _ _ _
  have hτW : τW ≫ j = τ := IsOpenImmersion.lift_fac _ _ _
  let q := j ≫ g
  have hσq : σW ≫ q = 𝟙 _ := by
    dsimp only [q]
    rw [← Category.assoc, hσW, hσ]
  have hτq : τW ≫ q = 𝟙 _ := by
    dsimp only [q]
    rw [← Category.assoc, hτW, hτ]
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsReduced (q.fiber s) := by infer_instance
  have hgeneric := connectedSpace_generic_fibre_of_flat_trait q
  have : ConnectedSpace (q ⁻¹' {η}) := (q.fiberHomeo η).connectedSpace_iff.mp hgeneric
  have hconn : _root_.IsPreconnected (q ⁻¹' {η}) := isPreconnected_iff_preconnectedSpace.mpr
    inferInstance
  have hmem (φ : Spec (.of R) ⟶ W.toScheme) (hφ : φ ≫ q = 𝟙 _) :
      φ η ∈ q ⁻¹' {η} := by
    change q (φ η) = η
    rw [← Scheme.Hom.comp_apply, hφ]
    rfl
  refine (hconn.image _ j.continuous.continuousOn).subset_connectedComponentIn
    ⟨σW η, hmem σW hσq, ?_⟩ ?_ ⟨τW η, hmem τW hτq, ?_⟩
  · exact congrArg (fun f : Spec (.of R) ⟶ P ↦ f η) hσW
  · rintro _ ⟨z, hz, rfl⟩
    exact hz
  · exact congrArg (fun f : Spec (.of R) ⟶ P ↦ f η) hτW

end AlgebraicGeometry
