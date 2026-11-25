/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve

import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Reduced cartesian compactification

Source: Stacks Project, etale-cohomology.tex, 03SD and 05K0.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- A finite etale cover of an open of a reduced curve has a reduced finite
compactification whose square over the original open is cartesian.

Source: Stacks Project 03SD (lemma-vanishing-easier), compactification paragraph;
05K0 (lemma-quasi-finite-separated-pass-through-finite).
(blueprint: r1-finite-etale-cover-reduced-cartesian-compactification)

Proof: Apply finite Zariski main theorem to v followed by j. Replace its finite
scheme by the reduced closure of the image of V. Since V is etale over the reduced
open U, it is reduced, and embeds openly in this reduced closure. The closed
immersion of the closure followed by the original finite morphism is finite.
Composition gives a separated finite-type k-scheme; integral incomparability
bounds its dimension by that of X. Over U the open V in the inverse image of U
is finite: a map into a separated U-scheme whose composite to U is finite is
finite. Its image is therefore closed. It is dense in that inverse image since
V is dense in the closure, hence surjective. A surjective open immersion is an
isomorphism, which identifies V with Y times_X U and gives the pullback square.
The empty-cover case gives the empty compactification and the same square. -/
theorem exists_reduced_cartesian_finite_cover_compactification
    {k : Type u} [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (v : V ⟶ U) [IsFinite v] [Etale v] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (a : V ⟶ Y),
      IsFinite p ∧ IsCurve (p ≫ f) ∧ IsReduced Y ∧ IsOpenImmersion a ∧
        IsPullback a v p j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsReduced U := isReduced_of_isOpenImmersion j
  have : IsReduced V := isReduced_of_etale v
  obtain ⟨T, i, q, hi, hic, hq, hiq⟩ :=
    (v ≫ j).exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have := hi
  have := hic
  have := hq
  -- The schematic image of a reduced scheme is already reduced.
  have : IsReduced i.image := IsSchemeTheoreticallyDominant.isReduced i.toImage
  let p := i.imageι ≫ q
  have : IsFinite p := inferInstance
  have : IsCurve (p ≫ f) :=
    { krullDim_le_one :=
        (topologicalKrullDim_le_of_continuous p.continuous
          fun _ _ ↦ p.eq_of_specializes_of_apply_eq).trans
            (IsCurve.krullDim_le_one (f := f)) }
  have hw : i.toImage ≫ p = v ≫ j := by
    dsimp [p]
    rw [i.toImage_imageι_assoc, hiq]
  -- Over U the comparison is both open and finite, hence has closed range.
  let b := pullback.lift i.toImage v hw
  have hbf : b ≫ pullback.fst p j = i.toImage := pullback.lift_fst _ _ _
  have hbs : b ≫ pullback.snd p j = v := pullback.lift_snd _ _ _
  have : IsOpenImmersion b := by
    have : IsOpenImmersion (b ≫ pullback.fst p j) := by rw [hbf]; infer_instance
    exact IsOpenImmersion.of_comp b (pullback.fst p j)
  have : IsFinite b := by
    have : IsFinite (b ≫ pullback.snd p j) := by rw [hbs]; infer_instance
    exact IsFinite.of_comp b (pullback.snd p j)
  have hr : ⇑(pullback.fst p j) ⁻¹' Set.range ⇑i.toImage = Set.range ⇑b := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (pullback.fst p j).isOpenEmbedding.injective
        (by rw [← Scheme.Hom.comp_apply, hbf, hx])⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [← Scheme.Hom.comp_apply, hbf]⟩
  -- Density in the compactification restricts to density in this open pullback.
  have hsurj : Function.Surjective b := by
    intro z
    have hz : pullback.fst p j z ∈ closure (Set.range ⇑i.toImage) := by
      rw [i.toImage.denseRange.closure_eq]
      trivial
    have hz' :=
      (pullback.fst p j).isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hz
    rw [hr, b.isClosedMap.isClosed_range.closure_eq] at hz'
    exact hz'
  have : IsIso b := by
    rw [isIso_iff_isOpenImmersion_and_epi_base]
    exact ⟨inferInstance, (TopCat.epi_iff_surjective b.base).mpr hsurj⟩
  refine ⟨i.image, p, i.toImage, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso b) hbf hbs

end AlgebraicGeometry.IsCurve
