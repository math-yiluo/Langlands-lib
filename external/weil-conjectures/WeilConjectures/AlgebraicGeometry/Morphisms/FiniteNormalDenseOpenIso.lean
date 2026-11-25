/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDenseOpen
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Comparing finite normal extensions on a dense open

## References

* Stacks Project, Tag 0BQL, integral-closure argument
* Stacks Project, Tag 0BQL, proof by integral closure, applied componentwise
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem extend_from_normalization {L X Y : Scheme.{u}}
    (n : X ⟶ L) (p : Y ⟶ L) [IsFinite p]
    (V : X.Opens) [QuasiCompact V.ι] [IsIso V.ι.fromNormalization]
    (a : V.toScheme ⟶ Y) (ha : a ≫ p = V.ι ≫ n) :
    ∃ f : X ⟶ Y, f ≫ p = n ∧ V.ι ≫ f = a := by
  let b := Limits.pullback.lift a V.ι ha
  let q := Limits.pullback.snd p n
  have hb : V.ι = b ≫ q := by simp [b, q]
  let d := V.ι.normalizationDesc b q hb
  let s := inv V.ι.fromNormalization ≫ d
  have hs : s ≫ q = 𝟙 X := by
    dsimp only [s, d]
    rw [Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  have hj : V.ι.toNormalization = V.ι ≫ inv V.ι.fromNormalization := by
    apply (cancel_mono V.ι.fromNormalization).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Hom.toNormalization_fromNormalization]
  have hc : V.ι ≫ s = b := by
    dsimp only [s]
    rw [← Category.assoc, ← hj, Hom.toNormalization_normalizationDesc]
  let f := s ≫ Limits.pullback.fst p n
  refine ⟨f, ?_, ?_⟩
  · dsimp only [f]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · dsimp only [f]
    rw [← Category.assoc, hc]
    simp [b]

/-- Finite normal schemes are determined over a locally Noetherian base by their
restriction to an open whose preimage is dense in both sources. -/
theorem finite_normal_iso_of_dense_open
    {L N E : Scheme.{u}} [IsLocallyNoetherian L]
    (n : N ⟶ L) (p : E ⟶ L) [IsFinite n] [IsFinite p]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (henormal : ∀ z : E, IsDomain (E.presheaf.stalk z) ∧
      IsIntegrallyClosed (E.presheaf.stalk z))
    (U : L.Opens)
    (hn : Dense (↑(n ⁻¹ᵁ U) : Set N))
    (hp : Dense (↑(p ⁻¹ᵁ U) : Set E))
    (e : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme)
    (he : e.hom ≫ (p ∣_ U) = n ∣_ U) :
    ∃ e' : N ≅ E, e'.hom ≫ p = n := by
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian n
  let : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  let : ∀ z : N, IsDomain (N.presheaf.stalk z) := fun z ↦ (hnormal z).1
  let : ∀ z : E, IsDomain (E.presheaf.stalk z) := fun z ↦ (henormal z).1
  let : IsReduced N := isReduced_of_isReduced_stalk N
  let : IsReduced E := isReduced_of_isReduced_stalk E
  let V := n ⁻¹ᵁ U
  let W := p ⁻¹ᵁ U
  let : IsDominant V.ι := ⟨by simpa [DenseRange, Opens.range_ι, V] using hn⟩
  let : IsDominant W.ι := ⟨by simpa [DenseRange, Opens.range_ι, W] using hp⟩
  let : IsIso V.ι.fromNormalization :=
    isIso_fromNormalization_denseOpen hnormal V hn
  let : IsIso W.ι.fromNormalization :=
    isIso_fromNormalization_denseOpen henormal W hp
  have ha : (e.hom ≫ W.ι) ≫ p = V.ι ≫ n := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, he, morphismRestrict_ι]
  have hai : (e.inv ≫ V.ι) ≫ n = W.ι ≫ p := by
    rw [Category.assoc, ← ha]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨f, hf, hfc⟩ := extend_from_normalization n p V (e.hom ≫ W.ι) ha
  obtain ⟨g, hg, hgc⟩ := extend_from_normalization p n W (e.inv ≫ V.ι) hai
  have hfg : f ≫ g = 𝟙 N := by
    refine ext_of_isDominant_of_isSeparated n ?_ V.ι ?_
    · simp [Category.assoc, hf, hg]
    · rw [← Category.assoc, hfc, Category.assoc, hgc]
      simp
  have hgf : g ≫ f = 𝟙 E := by
    refine ext_of_isDominant_of_isSeparated p ?_ W.ι ?_
    · simp [Category.assoc, hf, hg]
    · rw [← Category.assoc, hgc, Category.assoc, hfc]
      simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩


end AlgebraicGeometry.Scheme
