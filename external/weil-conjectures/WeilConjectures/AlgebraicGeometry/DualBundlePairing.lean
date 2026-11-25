/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-! # Dual vector bundles with their evaluation pairing

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/def-fd-kernel.md,
application paragraph (vector bundle, its dual, evaluation pairing `b(x,xi) = <x,xi>`);
used for the base-changed pairing in lem-fd-base-change.proof.md
(blueprint: def-fd-dual-bundle-pairing).

The simultaneous local charts give a bundle and its dual, including their evaluation.
Preservation of evaluation forces the transition functions of the two factors to be linear
and inverse-transpose. Thus these are dual frames, rather than arbitrary affine charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A rank-`r` vector bundle, its dual and evaluation function, presented in local dual
frames. The product chart formula is `sum x_i * xi_i`. The two cartesian squares identify
local total spaces with restrictions to the open cover. Empty covers on the empty base
and the empty coordinate sum in rank zero are allowed.
Source: latest blueprint, def-fd-kernel.md, application paragraph (dual bundle and
evaluation pairing) (blueprint: def-fd-dual-bundle-pairing). -/
structure DualBundlePairing {S V Vdual : Scheme.{u}} (π : V ⟶ S) (πdual : Vdual ⟶ S)
    (r : ℕ) (b : Γ(pullback π πdual, ⊤)) where
  I : Type u
  U : I → S.Opens
  cover : (⨆ i, U i) = ⊤
  localV : I → Scheme.{u}
  localDual : I → Scheme.{u}
  πV : ∀ i, localV i ⟶ (U i).toScheme
  πDual : ∀ i, localDual i ⟶ (U i).toScheme
  iV : ∀ i, localV i ⟶ V
  iDual : ∀ i, localDual i ⟶ Vdual
  squareV : ∀ i, IsPullback (iV i) (πV i) π (U i).ι
  squareDual : ∀ i, IsPullback (iDual i) (πDual i) πdual (U i).ι
  frameV : ∀ i, localV i ≅ AffineSpace (ULift.{u} (Fin r)) (U i).toScheme
  frameDual : ∀ i, localDual i ≅ AffineSpace (ULift.{u} (Fin r)) (U i).toScheme
  frameV_over : ∀ i, (frameV i).hom ≫
    (AffineSpace (ULift.{u} (Fin r)) (U i).toScheme ↘ (U i).toScheme) = πV i
  frameDual_over : ∀ i, (frameDual i).hom ≫
    (AffineSpace (ULift.{u} (Fin r)) (U i).toScheme ↘ (U i).toScheme) = πDual i
  evaluation : ∀ i,
    (pullback.map (πV i) (πDual i) π πdual (iV i) (iDual i) (U i).ι
      (squareV i).w.symm (squareDual i).w.symm).appTop b =
      ∑ j : Fin r,
        (pullback.fst (πV i) (πDual i) ≫ (frameV i).hom).appTop
          (AffineSpace.coord (U i).toScheme (ULift.up j)) *
        (pullback.snd (πV i) (πDual i) ≫ (frameDual i).hom).appTop
          (AffineSpace.coord (U i).toScheme (ULift.up j))

end AlgebraicGeometry
