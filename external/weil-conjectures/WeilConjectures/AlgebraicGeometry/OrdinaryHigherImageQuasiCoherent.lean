/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Ordinary higher direct images of quasi-coherent modules

Source: Stacks Project, Tag 01XJ (1).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Ordinary higher direct images preserve quasi-coherence for qcqs scheme morphisms.
Source: Stacks Project, Tag 01XJ (1).
(blueprint: lem-pc-ordinary-higher-image-quasi-coherent).

Proof:
Restrict to affine base opens; higher images commute with restriction and quasi-coherence
is local. The inverse image of an affine base open is qcqs. Apply the qcqs open induction
principle of Stacks Tag 08DR to the property P(U) that all ordinary higher images of all
quasi-coherent modules on the quasi-compact open U are quasi-coherent on the affine base.
For affine U, the morphism to the affine base is affine. Positive higher images vanish
by affine acyclicity; degree zero is quasi-coherent by localization of sections.
For U quasi-compact and V affine, assume P(U), P(V), and P(U ∩ V). Restriction preserves
quasi-coherence. Relative Mayer--Vietoris expresses each positive higher image on U ∪ V
as an extension of a cokernel and a kernel between the higher images on U, V, and U ∩ V.
Closure under finite sums, kernels, cokernels, and extensions proves P(U ∪ V); degree
zero follows from qcqs pushforward. Tag 08DR first inducts on separated opens, whose
affine intersections are affine, then on general qcqs opens: U ∩ V is a quasi-compact
separated open of V. This avoids assuming a smaller affine cover of arbitrary intersections.
Locality on the base completes the proof, including zero modules and empty schemes. -/
theorem ordinaryHigherImage_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (p : ℕ) :
    SheafOfModules.IsQuasicoherent.{u}
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M) := by
  let : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  let := hM
  exact Scheme.Modules.isQuasicoherent_higherDirectImage f M p

end AlgebraicGeometry
