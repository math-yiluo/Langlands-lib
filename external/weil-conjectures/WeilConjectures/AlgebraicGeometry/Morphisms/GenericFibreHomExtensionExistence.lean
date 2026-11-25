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
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
/-!
# Existence of extensions of generic-fibre morphisms

## References

* Stacks Project, Tag 0BQM, full faithfulness in the proof
* Stacks Project, Tag 0BQM, full faithfulness argument
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Existence part of finite étale generic-fibre hom extension. -/
theorem finiteEtale_genericFibre_hom_extension_exists {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ C) (πY : Y ⟶ C)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Cη) (πYη : Yη ⟶ Cη) (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX j) (hY : IsPullback ψY πYη πY j)
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃ f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by
  classical
  have : Nonempty C := ⟨Classical.choose (c.surjective (genericPoint S))⟩
  obtain ⟨hC, hη, hnC, hnη, e, he⟩ := smooth_connected_generic_geometry hS c q j hCη
  let : IsIntegral C := hC
  let : IsIntegral Cη := hη
  let k : Spec C.functionField ⟶ Cη := e.hom ≫ Cη.fromSpecStalk (genericPoint Cη)
  have hk : k ≫ j = C.fromSpecStalk (genericPoint C) := he
  let a := pullback.fst πXη k
  let b := pullback.fst πYη k
  let p := pullback.snd πXη k
  let r := pullback.snd πYη k
  have hA : IsPullback a p πXη k := IsPullback.of_hasPullback πXη k
  have hB : IsPullback b r πYη k := IsPullback.of_hasPullback πYη k
  let fg := hB.lift (a ≫ fη) p (by rw [Category.assoc, hfη]; exact hA.w)
  have hfg : fg ≫ r = p := hB.lift_snd _ _ _
  have hfgb : fg ≫ b = a ≫ fη := hB.lift_fst _ _ _
  have hAX : IsPullback (a ≫ ψX) p πX (C.fromSpecStalk (genericPoint C)) := by
    simpa only [hk] using hA.paste_horiz hX
  have hBY : IsPullback (b ≫ ψY) r πY (C.fromSpecStalk (genericPoint C)) := by
    simpa only [hk] using hB.paste_horiz hY
  obtain ⟨f, ⟨hf, hcompat⟩, _⟩ := finiteEtale_normalIntegral_generic_hom_full hnC
    πX πY p r (a ≫ ψX) (b ≫ ψY) hAX hBY fg hfg
  have : Etale πXη := MorphismProperty.of_isPullback hX inferInstance
  have : IsFinite πXη := MorphismProperty.of_isPullback hX inferInstance
  have : Etale πYη := MorphismProperty.of_isPullback hY inferInstance
  have : IsFinite πYη := MorphismProperty.of_isPullback hY inferInstance
  have hkg : IsPullback k e.hom (𝟙 Cη) (Cη.fromSpecStalk (genericPoint Cη)) :=
    IsPullback.of_vert_isIso ⟨by simp [k]⟩
  have hAη : IsPullback a (p ≫ e.hom) πXη (Cη.fromSpecStalk (genericPoint Cη)) := by
    simpa only [Category.comp_id] using hA.paste_vert hkg
  have hBη : IsPullback b (r ≫ e.hom) πYη (Cη.fromSpecStalk (genericPoint Cη)) := by
    simpa only [Category.comp_id] using hB.paste_vert hkg
  obtain ⟨u, _, hu⟩ := finiteEtale_normalIntegral_generic_hom_full hnη
    πXη πYη (p ≫ e.hom) (r ≫ e.hom) a b hAη hBη fg
    (by rw [← Category.assoc, hfg])
  let f' := hY.lift (ψX ≫ f) πXη (by rw [Category.assoc, hf]; exact hX.w)
  have hf' : f' ≫ πYη = πXη := hY.lift_snd _ _ _
  have hf'Y : f' ≫ ψY = ψX ≫ f := hY.lift_fst _ _ _
  have hrestrict : a ≫ f' = fg ≫ b := by
    apply hY.hom_ext
    · simpa only [Category.assoc, hf'Y] using hcompat
    · rw [Category.assoc, hf', hfgb, Category.assoc, hfη]
  have heq : f' = fη := (hu f' ⟨hf', hrestrict⟩).trans
    (hu fη ⟨hfη, hfgb.symm⟩).symm
  exact ⟨f, hf, hf'Y.symm.trans (congrArg (fun v ↦ v ≫ ψY) heq)⟩
end AlgebraicGeometry.Scheme
