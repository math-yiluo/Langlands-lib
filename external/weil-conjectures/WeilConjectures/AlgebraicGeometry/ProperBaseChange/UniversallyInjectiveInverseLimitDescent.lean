/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Descent of universal injectivity through an affine-transition inverse limit

## References

* Stacks Project, Limits, Tag 07RR and Morphisms, Tag 01S4, via surjectivity of the diagonal
* Stacks Project, Limits, Tag 07RR and Morphisms, Tag 01S4
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Universal injectivity of a finitely presented model descends from an inverse limit. -/
theorem exists_universallyInjective_pullback_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj (op i))] [QuasiSeparatedSpace (D.obj (op i))]
    {Y : Scheme.{u}} (p : Y ⟶ D.obj (op i))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (hp : UniversallyInjective (pullback.snd p (c.π.app (op i)))) :
    ∃ (j : I) (h : i ≤ j),
      UniversallyInjective (pullback.snd p (D.map (homOfLE h).op)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace ↥(pullback p p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace ↥(pullback p p) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  let γ : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p) (by simp)
  have : LocallyOfFinitePresentation γ.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.diagonal p))
  have hlim : UniversallyInjective (pullback.fst (c.π.app (op i)) p) := by
    have h := (MorphismProperty.cancel_left_of_respectsIso @UniversallyInjective
      (pullbackSymmetry (c.π.app (op i)) p).hom _).mpr hp
    simpa only [pullbackSymmetry_hom_comp_snd] using h
  have hdiag := (UniversallyInjective.iff_diagonal _).mp hlim
  rw [diagonal_pullback_fst] at hdiag
  have hγ : Surjective ((Over.pullback (c.π.app (op i))).map γ).left :=
    (MorphismProperty.cancel_right_of_respectsIso @Surjective _ _).mp
      ((MorphismProperty.cancel_left_of_respectsIso @Surjective _ _).mp hdiag)
  have : CompactSpace ↥((Over.mk p : Over (D.obj (op i))).left) :=
    inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace ↥((Over.mk p : Over (D.obj (op i))).left) :=
    inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj (op i))).left) :=
    inferInstanceAs (CompactSpace ↥(pullback p p))
  have : QuasiSeparatedSpace
      ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj (op i))).left) :=
    inferInstanceAs (QuasiSeparatedSpace ↥(pullback p p))
  obtain ⟨j, h, hj⟩ := exists_surjective_of_isLimit D c hc i
    (Over.mk p) (Over.mk (pullback.snd p p ≫ p)) γ hγ
  have hd : Surjective (pullback.diagonal (pullback.fst (D.map (homOfLE h).op) p)) := by
    rw [diagonal_pullback_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @Surjective _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso @Surjective _ _).mpr hj)
  have hf := (UniversallyInjective.iff_diagonal _).mpr hd
  refine ⟨j, h, ?_⟩
  have hs := (MorphismProperty.cancel_left_of_respectsIso @UniversallyInjective
    (pullbackSymmetry p (D.map (homOfLE h).op)).hom _).mpr hf
  simpa only [pullbackSymmetry_hom_comp_fst] using hs

end AlgebraicGeometry
