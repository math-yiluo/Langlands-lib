/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension

/-!
# Etale fibres of a flat morphism of finite presentation

## References

* Stacks Project, Tags 02GM, 02G8, and 02GK, and their pointwise algebra arguments
* Stacks Project, Tag 02GM, together with Tags 02G8 and
  02GK for unramifiedness and the pointwise etale criterion
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- For a flat morphism locally of finite presentation, an etale fibre is equivalent to
etale source neighbourhoods at all points over the chosen target point. -/
theorem etale_fibre_iff_forall_etale_neighbourhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (y : Y) :
    Etale (f.fiberToSpecResidueField y) ↔
      ∀ x : X, f x = y → ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)  := by
  classical
  constructor
  · intro hE x hxy
    subst y
    have := hE
    have hw : f.asFiber x ∈ (f.fiberToSpecResidueField (f x)).smoothLocus := by
      rw [(f.fiberToSpecResidueField (f x)).smoothLocus_eq_top]
      trivial
    have hx : x ∈ f.smoothLocus := by
      simpa using f.fiberι_mem_smoothLocus hw
    have hsm : Smooth (f.smoothLocus.ι ≫ f) := by
      apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
      rw [← Scheme.Hom.preimage_smoothLocus_eq]
      ext z
      simp
    have hd : topologicalKrullDimAt (f.asFiber x) = 0 :=
      topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
        (f.fiberToSpecResidueField (f x)) 0 (f.asFiber x)
    obtain ⟨V, -, hxV, hV⟩ :=
      exists_etale_open_of_smooth_of_fibre_dimension_zero f x f.smoothLocus hx hsm hd
    exact ⟨V, hxV, hV⟩
  · intro h
    let g := f.fiberToSpecResidueField y
    let W (V : X.Opens) := (f.fiberι y) ⁻¹ᵁ V
    have hxy (w : f.fiber y) : f (f.fiberι y w) = y :=
      (f.range_fiberι y).subset ⟨w, rfl⟩
    choose V hwV hV using fun w : f.fiber y ↦ h (f.fiberι y w) (hxy w)
    apply IsZariskiLocalAtSource.of_iSup_eq_top (fun w ↦ W (V w))
    · apply top_unique
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwV w⟩
    · intro w
      have hpb : IsPullback (f.fiberι y ∣_ V w) ((W (V w)).ι ≫ g)
          ((V w).ι ≫ f) (Y.fromSpecResidueField y) :=
        (isPullback_morphismRestrict (f.fiberι y) (V w)).paste_vert
          (IsPullback.of_hasPullback _ _)
      exact CategoryTheory.MorphismProperty.of_isPullback hpb (hV w)

end AlgebraicGeometry.Scheme
