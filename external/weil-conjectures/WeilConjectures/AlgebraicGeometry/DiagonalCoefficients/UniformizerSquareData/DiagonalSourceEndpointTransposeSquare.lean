/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalSourceEndpointLeftTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalSourceEndpointRightTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalDerivedSourceNormalization

/-! # Equality of the two actual endpoint transposes

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-source-endpoint-transpose-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- The two actual endpoint morphisms have equal cyclic-adjunction transposes.
Source: coefficient changes (1). (blueprint: lem-diagonal-source-endpoint-transpose-square).
Proof: the left endpoint transpose is the extended quotient source transpose.
The normalized derived source square identifies it with the extended cyclic source
transpose. The inverse right endpoint transpose identity finishes the equality. -/
theorem source_endpoint_transpose_square
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) :
    q.cyclicAdjunction.homEquiv _ _ (q.sourceEndpointLeft s) =
      q.cyclicAdjunction.homEquiv _ _ (q.sourceEndpointRight s) := by
  exact (q.source_endpoint_left_transpose s).trans
    ((q.source_transpose_square s hs).trans (q.source_endpoint_right_transpose s).symm)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
