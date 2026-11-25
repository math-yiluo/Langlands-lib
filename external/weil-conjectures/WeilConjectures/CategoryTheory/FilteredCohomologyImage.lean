/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

/-! # The cohomology image filtration

Source: Stacks Project, Tags 012P and 012W.
(blueprint: lem-sp-filtered-cohomology-image-finite).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (L : DecreasingFiltration K)



private theorem complexStep_antitone (n : ℤ) : Antitone (fun p ↦ L.complexStep p n) := by
  intro p q hpq
  have h := imageSubobject_comp_le
    ((Subobject.ofLE (L.step q) (L.step p) (L.antitone_step hpq)).f n)
    ((L.step p).arrow.f n)
  simpa only [complexStep, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow] using h

/-- Degreewise finite filtrations induce a finite cohomology image filtration.
Source: Stacks Project, Tag 012W, using the image filtration in Tag 012P.
(blueprint: lem-sp-filtered-cohomology-image-finite).

Proof. Take the minimum of the lower bounds in degrees n-1, n and n+1.
Antitonicity makes all three steps at this minimum top. The inclusion of this
subcomplex is an isomorphism in those three degrees; hence its map on H^n is
an isomorphism and its image is top. At the upper bound in degree n the
subcomplex has zero term, so its H^n is zero and the image is bottom. -/
theorem cohomologyImage_isFinite
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      L.complexStep lo n = ⊤ ∧ L.complexStep hi n = ⊥)
    (n : ℤ) : (L.homologyFiltration n).IsFinite := by
  obtain ⟨a, _, ha, _⟩ := hfinite ((ComplexShape.up ℤ).prev n)
  obtain ⟨b, z, hb, hz⟩ := hfinite n
  obtain ⟨d, _, hd, _⟩ := hfinite ((ComplexShape.up ℤ).next n)
  let lo := min a (min b d)
  have htop (i : ℤ) (k : ℤ) (hk : L.complexStep k i = ⊤) (hlo : lo ≤ k) :
      L.complexStep lo i = ⊤ := by
    apply top_unique
    rw [← hk]
    exact L.complexStep_antitone i hlo
  have iso (i : ℤ) (hi : L.complexStep lo i = ⊤) :
      IsIso ((L.step lo).arrow.f i) := by
    apply (Subobject.isIso_iff_mk_eq_top _).2
    rwa [← imageSubobject_mono, ← complexStep]
  have := iso _ (htop _ _ ha (min_le_left _ _))
  have := iso n (htop _ _ hb (le_trans (min_le_right _ _) (min_le_left _ _)))
  have := iso _ (htop _ _ hd (le_trans (min_le_right _ _) (min_le_right _ _)))
  let f := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
    (L.step lo).arrow
  have : IsIso f.τ₁ := by
    change IsIso ((L.step lo).arrow.f ((ComplexShape.up ℤ).prev n))
    infer_instance
  have : IsIso f.τ₂ := by
    change IsIso ((L.step lo).arrow.f n)
    infer_instance
  have : IsIso f.τ₃ := by
    change IsIso ((L.step lo).arrow.f ((ComplexShape.up ℤ).next n))
    infer_instance
  have : IsIso f := ShortComplex.isIso_of_isIso f
  have : QuasiIsoAt (L.step lo).arrow n := by
    rw [quasiIsoAt_iff]
    change ShortComplex.QuasiIso f
    infer_instance
  have : IsIso (HomologicalComplex.homologyMap (L.step lo).arrow n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have hzero : (L.step z).arrow.f n = 0 := by
    apply (Subobject.mk_eq_bot_iff_zero).1
    rwa [← imageSubobject_mono, ← complexStep]
  have hx : IsZero ((L.step z : CochainComplex C ℤ).X n) :=
    IsZero.of_mono_eq_zero _ hzero
  have hh := (HomologicalComplex.ExactAt.of_isZero hx).isZero_homology
  refine ⟨lo, z, ?_, ?_⟩
  · change imageSubobject (HomologicalComplex.homologyMap (L.step lo).arrow n) = ⊤
    exact (imageSubobject_mono _).trans (Subobject.mk_eq_top_of_isIso _)
  · change imageSubobject (HomologicalComplex.homologyMap (L.step z).arrow n) = ⊥
    have he : HomologicalComplex.homologyMap (L.step z).arrow n = 0 := hh.eq_of_src _ _
    rw [he, imageSubobject_zero]

end CategoryTheory.DecreasingFiltration
