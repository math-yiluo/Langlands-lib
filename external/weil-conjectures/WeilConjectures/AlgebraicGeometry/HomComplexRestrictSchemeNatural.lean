/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents

/-! # Naturality of restriction of the ordinary internal Hom complex

Source: Stacks Project, Cohomology, Tag 08DL. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Restriction of ordinary internal Hom is natural in the second complex.
Source: Stacks Project, Cohomology, Tag 08DL, the ordinary Hom computation in its proof.
(blueprint: lem-sc-hom-complex-restrict-scheme-natural).

Proof: Restrict local module maps to the over-U site and transport them through
`Scheme.Modules.overEquiv U`. For each source degree and target degree, the sheaf
Hom identification commutes with postcomposition by every map of target complexes.
Restriction preserves the products defining each total degree. The identifications
intertwine both terms of the Hom differential, since restriction preserves composition
and addition. They therefore define chain isomorphisms. Their postcomposition
compatibility is the naturality square in the second complex. The construction
includes unbounded complexes, zero complexes and the empty open. -/
theorem homComplex_restrict_scheme_natural {Y : Scheme.{u}} (U : Y.Opens)
    (L : CochainComplex Y.Modules ℤ) :
    Nonempty (
      (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L) ⋙
          (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ≅
      (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj
          (op (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj
            L))) := by
  obtain ⟨e, he⟩ := homComplex_restrict_scheme_natural_components U L
  exact ⟨CategoryTheory.NatIso.ofComponents e (by
    intro M N f
    exact he f)⟩


end AlgebraicGeometry
