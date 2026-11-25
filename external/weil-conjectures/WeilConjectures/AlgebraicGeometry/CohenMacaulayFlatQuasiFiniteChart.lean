/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AffineBaseFlatQuasiFiniteChartCore

/-! # Flat quasi-finite charts at Cohen-Macaulay fibre points

Source: Stacks Project, proof of Tag 00RH.
(blueprint: lem-sbc-cohen-macaulay-flat-quasi-finite-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A Cohen-Macaulay fibre point admits a flat quasi-finite chart over a smooth base model.

Source: Stacks Project, proof of Tag 00RH, using Tags 00QE, 00RE, 00R7 and 00RC.
Proof: Choose an affine base neighbourhood inside U and an affine source neighbourhood
of y over it. The resulting ring map R to S is flat and finitely presented.
The fibre at y is locally of finite type over the residue field. The dimension-at-point
formula 0A21 (10) makes its local topological dimension a finite integer n.
By 00QE, after a principal source shrinking, there is a quasi-finite R-algebra map
R[t_1,...,t_n] to S. Its fibre map at y is flat by 00RE: the source local ring is
regular, the target is Cohen-Macaulay by hdepth, and quasi-finiteness together with
00P1 makes the local-ring dimensions equal (the residue extension is finite).
The fibrewise flatness criterion 00R7 makes the polynomial map flat at y.
Since this map is finitely presented, 00RC permits another principal shrinking on
which it is flat everywhere. It stays quasi-finite and finitely presented.
Take O to be this affine source open, P to be affine n-space over the chosen affine
base open, h the spectrum map and g the projection followed by the base open inclusion.
Then g is smooth of relative dimension n, and h followed by g is O.ι followed by f.
The stalk identification used in applying hdepth is the open-fibre stalk isomorphism.
An empty source or empty U has no point satisfying ht, so requires no chart.
(blueprint: lem-sbc-cohen-macaulay-flat-quasi-finite-chart) -/
theorem exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (y : X) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens) (P : Scheme.{u}) (h : O.toScheme ⟶ P) (g : P ⟶ T),
      y ∈ O ∧ Flat h ∧ LocallyQuasiFinite h ∧ LocallyOfFinitePresentation h ∧
        SmoothOfRelativeDimension n g ∧ h ≫ g = O.ι ≫ f := by
  obtain ⟨n, O, V, hV, e, hy, heflat, heqf, helfp, he⟩ :=
    exists_affine_base_flat_quasiFinite_chart_core f U y ht hdepth
  let P := AffineSpace (ULift.{u} (Fin n)) V.toScheme
  let g : P ⟶ T := (P ↘ V.toScheme) ≫ V.ι
  have hsm : SmoothOfRelativeDimension n g := by
    have h1 : SmoothOfRelativeDimension n (P ↘ V.toScheme) := by
      simpa [P] using
        (AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V.toScheme)
    let _ : SmoothOfRelativeDimension n (P ↘ V.toScheme) := h1
    exact smoothOfRelativeDimension_comp (n := n) (m := 0) (P ↘ V.toScheme) V.ι
  refine ⟨n, O, P, e, g, hy, heflat, heqf, helfp, hsm, ?_⟩
  change e ≫ (P ↘ V.toScheme) ≫ V.ι = O.ι ≫ f
  exact he

end AlgebraicGeometry
