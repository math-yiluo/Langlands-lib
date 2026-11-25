/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Étale near a point smooth of fibre dimension zero

Source: Stacks Project, Tag 0A43, final sentence of the proof; Tags 02G1, 02G2 and
02GI (blueprint: lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism smooth on an open neighbourhood of `x`, whose scheme-theoretic fibre has
local dimension zero at `x`, is étale on a smaller open neighbourhood contained in the given one.
Source: Stacks Project, Tag 0A43, final sentence of the proof, and Tags 02G1, 02G2, 02GI
(blueprint: lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension).

Proof:
1. The fibre of `U.ι ≫ f` is an open subscheme of the fibre of `f`
   (lem-weil-pbc-open-fibre-product, def-pc-scheme-fibre). The corresponding point lies in
   this open, and its local dimension is unchanged
   (lem-weil-pbc-dimension-at-point-open-subspace, def-kun-topological-dimension-at-point).
   Thus the dimension of the restricted fibre at that point is zero.
2. Apply lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension to the smooth restriction.
   On suitable affine neighbourhoods in source and target, the Kähler differential module
   (def-weil-pbc-kahler-differentials) is free of rank equal to that fibre dimension, hence of
   rank zero. It is therefore zero (Stacks 02G1, 01UT).
3. Apply lem-weil-pbc-smooth-zero-differentials-affine-open-etale: smoothness and vanishing
   differentials imply that the source affine neighbourhood maps étale to `S` (Stacks 00U1,
   02GI). This neighbourhood is open in `U`, hence open in `X`, contains `x`, and is contained
   in `U`. It is the required `U'`. -/
theorem exists_etale_open_of_smooth_of_fibre_dimension_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (U : X.Opens) (hx : x ∈ U)
    (hSmooth : Smooth (U.ι ≫ f)) (hDim : topologicalKrullDimAt (f.asFiber x) = 0) :
    ∃ U' : X.Opens, U' ≤ U ∧ x ∈ U' ∧ Etale (U'.ι ≫ f) := by
  -- Use the source library’s relative-dimension charts instead of differential modules.
  let g := U.ι ≫ f
  let xU : U := ⟨x, hx⟩
  obtain ⟨A, B, -, -, hxB, e, d, hd⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE g xU
  have : SmoothOfRelativeDimension d (B.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    have : SmoothOfRelativeDimension (d + 0) (g.resLE A B e ≫ A.ι) := inferInstance
    simpa using this
  let V : X.Opens := U.ι ''ᵁ B
  have hV : V ≤ U := U.ι_image_le B
  have hxV : x ∈ V := (U.mem_ι_image_iff).mpr hxB
  have hrel : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← U.ι.isoImage_inv_ι B, Category.assoc]
    have : SmoothOfRelativeDimension (0 + d)
        ((U.ι.isoImage B).inv ≫ B.ι ≫ g) := inferInstance
    simpa [g, Category.assoc] using this
  let W := (f.fiberι (f x)) ⁻¹ᵁ V
  have hxW : f.asFiber x ∈ W := by
    change f.fiberι _ (f.asFiber x) ∈ V
    simpa using hxV
  have hpb : IsPullback (f.fiberι (f x) ∣_ V)
      (W.ι ≫ f.fiberToSpecResidueField (f x))
      (V.ι ≫ f) (S.fromSpecResidueField (f x)) :=
    (isPullback_morphismRestrict (f.fiberι (f x)) V).paste_vert
      (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  have hlocal := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
    (W.ι ≫ f.fiberToSpecResidueField (f x)) d (⟨f.asFiber x, hxW⟩ : W)
  rw [IsOpen.topologicalKrullDimAt_eq W.isOpen hxW, hDim] at hlocal
  have hd0 : d = 0 := by exact_mod_cast hlocal.symm
  subst d
  exact ⟨V, hV, hxV, (Etale.iff_smoothOfRelativeDimension_zero _).mpr hrel⟩

end AlgebraicGeometry
