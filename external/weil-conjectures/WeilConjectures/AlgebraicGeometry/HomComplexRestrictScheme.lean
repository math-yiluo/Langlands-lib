/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictSchemeTransport
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv

/-! # Ordinary internal Hom complexes on an open subscheme

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom.
(blueprint: lem-sc-hom-complex-restrict-scheme). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Ordinary internal Hom commutes with restriction to an open subscheme.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Mathlib's `Scheme.Modules.overFunctorEquiv` and `Scheme.Modules.overEquiv`.
(blueprint: lem-sc-hom-complex-restrict-scheme).

Proof: First restrict both complexes to the over-U site. The isomorphism
`homComplex_restrict_open` identifies the Hom complex there with the restriction
of the ambient Hom complex. Transport this isomorphism through `overEquiv U`.
This equivalence identifies internal Homs: a module map on an open of U is the
same local linear map on its image open in Y, with scalars transported along
U.ι.appIso. These identifications commute with restrictions, precomposition and
postcomposition. In each degree, use preservation of products by the equivalence
to identify the product over p of Hom(L.X p,M.X (p+n)). Compatibility with the
two compositions and additivity identify the differential d_M f - (-1)^n f d_L.
The resulting component isomorphisms define a chain isomorphism. Finally use
`overFunctorEquiv U` on L, M and their Hom complex to replace the composite
restriction and equivalence by `restrictFunctor U.ι`. No boundedness is needed;
products indexed by all integers are preserved. Rank zero, zero complexes and
empty U are included. -/
theorem homComplex_restrict_scheme {Y : Scheme.{u}} (U : Y.Opens)
    (L M : CochainComplex Y.Modules ℤ) :
    Nonempty (
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := Y.toRingedSpace.sheaf) L M) ≅
      homComplex (R := U.toScheme.toRingedSpace.sheaf)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M)) := by
  obtain ⟨e, he⟩ := internalHom_overEquiv U
  exact homComplex_restrict_scheme_of_homIso U L M e he

end AlgebraicGeometry
