/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Use the affine K-flat theorem with its ring kept bundled.

Source: Stacks Tag 08DV, associated sheaves of bounded-above flat resolutions.
Destruct the bundled ring and apply tensorResolution_isKFlat to its underlying
commutative ring. The resulting complex and scheme are definitionally the given
ones. Keeping this repackaging named avoids repeatedly normalizing Spec of a
rebuilt bundled ring in clients of the comparison construction.

(blueprint: new-h4-qcoh-kflat-bundled-ring) -/
theorem tensorResolution_isKFlat_bundledRing
    (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    CochainComplex.IsKFlatTensor (R := (Spec A).sheaf)
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj
        (P.complex.extend ComplexShape.embeddingDownNat)) := by
  cases A
  exact tensorResolution_isKFlat _ M P

end AlgebraicGeometry
