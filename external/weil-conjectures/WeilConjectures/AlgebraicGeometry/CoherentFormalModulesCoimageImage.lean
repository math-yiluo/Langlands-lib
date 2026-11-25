/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # CoherentFormalModulesCoimageImage

Source: Stacks Project, Lemma 087X (blueprint: lem-weil-pbc-coherent-formal-coimage-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical coimage-image comparison for coherent adic systems is invertible,
for any choices of the kernel and cokernel structures.
Source: Stacks Project, Lemma 087X, paragraph proving Coim=Im.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image).

Proof: Use the stabilized kernel construction of claims (a)--(d) in 087X and
the termwise cokernel construction. They commute with restriction to an affine
open: coherent kernels, images, ideal products, and quotients commute with such
restriction, and the stabilization constant can be enlarged without changing the
resulting universal kernel. The affine equivalence 087W identifies the resulting
kernel with the finite module ker f over the Noetherian completion, and the
cokernel with coker f. Finiteness follows from Noetherianity. Hence on an affine
cover the coimage is M/ker f and the image is im f, and the canonical comparison
is the map induced by f. The first isomorphism theorem for modules makes this
map invertible. The affine equivalence reflects isomorphisms. The resulting
comparison is componentwise an isomorphism locally on X, hence globally, and
component inverses form a natural transformation. Finally any other choices of
kernels and cokernels are uniquely isomorphic to these universal constructions;
these isomorphisms conjugate the canonical comparison. Thus the conclusion holds
for the arbitrary HasKernels and HasCokernels instances in the statement. This
argument does not identify the formal kernel with the termwise kernel. Zero
arrows, zero systems, and the empty scheme satisfy the same universal argument.
-/
theorem coherentFormalModules_coimageImage_isIso (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)]
    {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison α) := by
  exact (coherentFormalModule_isIso_of_isIso_restrict I
    (fun U : X.affineOpens ↦ (U : X.Opens)) (iSup_affineOpens_eq_top X)
    (Abelian.coimageImageComparison α)
    (fun U n ↦ coherentFormalModules_coimageImage_isIso_restrict_affine X I U α n)).1

end AlgebraicGeometry
