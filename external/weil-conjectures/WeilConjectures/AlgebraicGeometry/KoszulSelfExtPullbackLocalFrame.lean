/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtQuotientFrame
import WeilConjectures.AlgebraicGeometry.ClosedImmersionQuotientFramePullback

/-! # A finite free chart for self Ext after tensor pullback

Source: Stacks Project, Tag 0BQY, Lemma 48.15.4, zero-differential Hom calculation.
(blueprint: lem-sc-koszul-self-ext-pullback-local-frame). -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On a Koszul-regular affine chart, the pulled-back self Ext sheaf is free on
increasing subsets of the given generators. This is a sheaf assertion on the chart;
no stalk, auxiliary open restriction, or conormal dual is involved.

Source: Stacks Project, Tag 0BQY, Lemma 48.15.4, proof through the displayed
identification of self Ext with Hom from the degree minus n Koszul term.
(blueprint: lem-sc-koszul-self-ext-pullback-local-frame).

Proof: Put A = Gamma(Y,U), I = ker(i)(U), and B = A/I. The closed immersion on
this affine chart identifies its inverse image with Spec B over Spec A. Use
exists_koszul_projective_resolution to obtain the actual augmented Koszul complex
K resolving B, whose nth term is the nth exterior power of the free A-module A^m.
Sheafify the augmentation using exists_affine_quotient_sheafified_resolution and
reindex the nonnegative chain complex as a nonpositive cochain complex. Each term
has the increasing exterior basis, so it is finite free, and the complex is bounded
above. Restrict derived internal Hom to U. Apply the bounded-above finite-free Hom
model with target the single complex of the restricted pushforward of O_Z. Its
only term in degree n is Hom_A(K_n,B). Its differential is zero: precomposition
with the Koszul differential has coefficients f_j, each of which annihilates B.
Thus its nth cohomology is that term, with the dual increasing wedge basis over B.
The coefficient maps and basis identifications commute with localization, so they
identify the restricted self Ext sheaf with the associated sheaf of the free
B-module indexed by n-element subsets. Ordinary tensor pullback along Spec B to
Spec A leaves this quotient module unchanged: B tensor_A B is B, via multiplication
and its inverse b maps to 1 tensor b. Transport across the chart and the equivalence
with its over site to obtain the stated free sheaf frame, reindexed by ULift.
If the supplied derived universe differs from the natural resolution universe,
compute both Hom objects using the same K-injective resolution; the localization
comparisons identify their cohomology with the same finite-free Hom complex.
The degree-zero index consists of the empty subset; above m it is empty and the
Koszul term is zero. The argument remains valid for m=0 and B=0, including an empty
inverse-image chart. It uses regularity only on U and chooses no arbitrary object
from an unproved existence theorem. -/
theorem koszulRegularImmersion_self_ext_pullback_local_frame
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (U : Y.affineOpens) (n : ℕ)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    Nonempty ((((Scheme.Modules.tensorPullback i).obj G).over (i ⁻¹ᵁ U.1)) ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin m) n))) := by
  classical
  dsimp only
  obtain ⟨e⟩ := koszul_self_ext_quotient_frame i U n m f hf hreg
  exact closedImmersion_quotient_frame_pullback i U.1 _ _ e

end AlgebraicGeometry
