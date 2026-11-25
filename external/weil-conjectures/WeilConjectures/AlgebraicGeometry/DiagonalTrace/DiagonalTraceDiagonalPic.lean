/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.ProjectiveLineAutomorphismHyperplane

/-! # The diagonal divisor line relative to an arbitrary projective-line model

Source: the diagonal equation in the proof of lem-amb-p1-diagonal-chern-components;
EGA II, Remark 4.2.7, and its arbitrary-base extension in the projective-bundle
Picard classification (Stacks, Tag 0B8W), for changing the projective-line model.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

attribute [local irreducible] ProjectiveSpace

private theorem diagonalPic_canonical (Y : Scheme.{u}) (a : Bool) :
    Scheme.Pic.map (Etale.projectiveLineDiagonalChart Y a).val.hom (diagonalPic Y) =
      hyperplanePic (ProjectiveLine Y) *
        Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y)
          (hyperplanePic Y) := by
  exact Etale.finiteP1_diagonal_picard Y (diagonalImmersion_cartier Y) a

private theorem pic_map_ofIsInvertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) := by
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso L)⟩

private theorem pic_map_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (Scheme.Pic.map e.hom) := by
  intro L M h
  have h' := congrArg (Scheme.Pic.map e.inv) h
  simpa only [← Scheme.Pic.map_comp, Iso.inv_hom_id, Scheme.Pic.map_id] using h'

/-- The diagonal divisor has relative degree one in either projection, including after
changing its projective-line model. Its remaining factor is pulled back from the base.

Source: lem-amb-p1-diagonal-chern-components, proof, the equation x0 y1 - x1 y0;
EGA II, Remark 4.2.7, with the arbitrary-base projective bundle Picard
classification (Stacks, Tag 0B8W, finite-presentation descent).
(blueprint: lem-sfb-diagonal-trace-diagonal-pic).

Proof: the four standard product charts identify the dual diagonal ideal with
pr1* O(1) tensor pr2* O(1): the section x0 y1 - x1 y0 cuts out the diagonal
and its transition units are exactly those of this tensor product. Thus the
line has degree one on every fibre of either projection. Transport along e.
The projective bundle Picard classification writes the transported line as
O(d) tensor the pullback of a base line. Restriction to every residue-field
fibre shows d = 1, because e is an isomorphism over the base and the diagonal
is a section of f. Pull back this decomposition along e and use he to identify
the base pullback with f*. Passing to Picard classes gives the stated product.
The statement includes disconnected and nonreduced bases: the locally constant
degree function is one on every component. On the empty base all Picard classes
are the unit, and the base unit module supplies the witness. -/
theorem diagonalTrace_diagonalPic_factorization (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (e : diagonalSurface Y ≅ ProjectiveLine (ProjectiveLine Y))
    (he : e.hom ≫ (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) = f) :
    ∃ (L : (ProjectiveLine Y).Modules) (hL : Scheme.Modules.IsInvertible L),
      letI := hL
      diagonalPic Y =
        Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) *
          Scheme.Pic.mapHom e.hom (hyperplanePic (ProjectiveLine Y)) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Bool, f = Etale.projectiveLineDiagonalProjection Y a := by
    rcases hf with hf | hf
    · exact ⟨false, hf⟩
    · exact ⟨true, hf⟩
  let c := (Etale.projectiveLineDiagonalChart Y a).val
  have hc : c.hom ≫ f = (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) := by
    rw [ha]
    exact (Etale.projectiveLineDiagonalChart Y a).property
  let g := c ≪≫ e
  have hg : g.hom ≫ (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) =
      (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) := by
    change (c.hom ≫ e.hom) ≫ _ = _
    rw [Category.assoc, he, hc]
  obtain ⟨B, hB⟩ := ProjectiveLine.automorphism_hyperplane (ProjectiveLine Y) g hg
  let C : (ProjectiveLine Y).Pic := hyperplanePic Y * B⁻¹
  let L := (fromSkeleton (ProjectiveLine Y).Modules).obj C.val
  have hL : Scheme.Pic.ofIsInvertible L = C := Scheme.Pic.ofIsInvertible_fromSkeleton C
  refine ⟨L, inferInstance, ?_⟩
  apply pic_map_injective c
  rw [diagonalPic_canonical, Scheme.Pic.map_mul, ← pic_map_ofIsInvertible,
    ← Scheme.Pic.map_comp, hc, hL]
  change _ = _ * Scheme.Pic.map c.hom (Scheme.Pic.map e.hom (hyperplanePic _))
  rw [← Scheme.Pic.map_comp]
  change _ = _ * Scheme.Pic.map g.hom (hyperplanePic _)
  have hB' : Scheme.Pic.map g.hom (hyperplanePic (ProjectiveLine Y)) =
      Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) B *
        hyperplanePic (ProjectiveLine Y) := by
    simpa only [hyperplanePic, Scheme.Pic.ofIsInvertible] using hB
  rw [hB']
  change _ = Scheme.Pic.map _ (hyperplanePic Y * B⁻¹) * _
  rw [Scheme.Pic.map_mul]
  change _ = _ * (Scheme.Pic.mapHom _ B⁻¹) * _
  rw [map_inv]
  change hyperplanePic (ProjectiveLine Y) *
      Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y)
        (hyperplanePic Y) =
    (Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y)
        (hyperplanePic Y) *
      (Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) B)⁻¹) *
      (Scheme.Pic.map (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) B *
        hyperplanePic (ProjectiveLine Y))
  rw [mul_assoc, inv_mul_cancel_left, mul_comm]

end AlgebraicGeometry.ProEtale.DiagonalTrace
