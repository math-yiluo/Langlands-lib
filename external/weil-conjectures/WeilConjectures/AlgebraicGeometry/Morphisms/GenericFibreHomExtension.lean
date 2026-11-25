/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreHomExtensionExistence
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreCoverDensity
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Full faithfulness of generic-fibre restriction for finite étale covers

## References

* Stacks Project, Tag 0BQM, proof (full faithfulness over the generic point)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction to the generic fibre is fully faithful on finite étale covers of a
smooth family with geometrically connected fibres over an integral normal base. -/
theorem finiteEtale_genericFibre_hom_extension {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ C) (πY : Y ⟶ C)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Cη) (πYη : Yη ⟶ Cη) (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX j) (hY : IsPullback ψY πYη πY j)
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by
  obtain ⟨f, hf⟩ := finiteEtale_genericFibre_hom_extension_exists hS c q j hCη
    πX πY πXη πYη ψX ψY hX hY fη hfη
  refine ⟨f, hf, ?_⟩
  intro g hg
  obtain ⟨hred, hdom⟩ := genericFibre_cover_reduced_and_dominant c q j hCη
    πX πXη ψX hX
  let : IsReduced X := hred
  let : IsDominant ψX := hdom
  exact AlgebraicGeometry.ext_of_isDominant_of_isSeparated πY (hg.1.trans hf.1.symm)
    ψX (hg.2.trans hf.2.symm)

end AlgebraicGeometry.Scheme
