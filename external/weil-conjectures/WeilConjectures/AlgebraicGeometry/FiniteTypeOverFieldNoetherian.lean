/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherian spaces for schemes of finite type over a field

This small interface supplies the geometric hypothesis for the inherited shift on bounded
constructible complexes without importing the six-functor triangulatedness package.
Source: the finite-type ambient setting of the latest blueprint, order 4192
(blueprint: lem-per-finite-type-over-field-noetherian).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme of finite type over a field has Noetherian underlying space.
Proof: the field spectrum is Noetherian. Local finite type therefore gives a locally
Noetherian source, and quasi-compactness of the structure map gives a compact source.
Together these make the source a Noetherian scheme, hence a Noetherian space.
Source: latest blueprint, order 4192, finite-type ambient setting; Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian`, `QuasiCompact.compactSpace_of_compactSpace`, and
`IsNoetherian.noetherianSpace`
(blueprint: lem-per-finite-type-over-field-noetherian). -/
instance finiteTypeOverField_noetherianSpace {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    TopologicalSpace.NoetherianSpace X.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  infer_instance

end AlgebraicGeometry
