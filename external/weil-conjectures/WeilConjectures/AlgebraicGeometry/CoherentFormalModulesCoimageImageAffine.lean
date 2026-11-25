/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineMono
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineEpi

/-! # Affine-local coimage-image comparison

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On one affine open and at one positive level, the coimage-image comparison
of coherent formal modules restricts to an isomorphism of module sheaves.
Source: Stacks Project, Lemma 087X, affine kernel calculation and final paragraph
of part (1), using Lemma 087W.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image-affine).

Proof: Write U = Spec A and J for the ideal corresponding to I restricted to U.
Restriction preserves coherence, ideal products and quotients, so the restricted
systems correspond under 087W to finite modules M and N over the J-adic completion
B of A. Write f for the induced B-linear map and K for its kernel. B is Noetherian,
so K is finite. In the stabilized kernel construction of 087X, Artin-Rees gives c
such that the eventual image at level m is K/(K intersect J^m M), and its quotient
by J^r is K/J^r K for m at least r+c. Restriction to U commutes with these images
and quotients; increasing the global stabilization bounds to these affine bounds
does not change the eventual objects or their universal maps. Thus the restricted
formal kernel is the quotient system of K, not the system of termwise kernels.
Termwise cokernels correspond to coker f, since quotient reduction is right exact.
Apply these observations also to the kernel inclusion and cokernel projection:
the restricted coimage and image are the quotient systems of M/K and im f. Their
canonical comparison is induced by the map M/K to im f, as follows by composing
with the cokernel projection and kernel inclusion and using their universal
properties. The module first isomorphism theorem gives its inverse. Reducing that
inverse modulo J^(n+1) and taking the associated sheaf gives a two-sided inverse
at the stated level. Arbitrary supplied kernel and cokernel structures are uniquely
isomorphic to the constructed ones; the universal maps identify their comparisons
by conjugation, preserving invertibility. This proves the claim on the single open
U without using any global gluing or assuming an abelian structure on Coh(X,I).
For the empty affine open all module sheaves are zero and the same argument applies.
Zero arrows and the ideals zero and one likewise require no additional hypothesis.
-/
theorem coherentFormalModules_coimageImage_isIso_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  let φ := (Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
    ((Abelian.coimageImageComparison α).hom.app (op n))
  have : Mono φ := coherentFormalModules_coimageImage_isMono_restrict_affine X I U α n
  have : Epi φ := coherentFormalModules_coimageImage_isEpi_restrict_affine X I U α n
  exact isIso_of_mono_of_epi φ

end AlgebraicGeometry
