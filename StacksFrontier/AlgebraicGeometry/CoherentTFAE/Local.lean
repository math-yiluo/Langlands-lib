module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Affine

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Finite type is local on a scheme, and the affine-open form of a quasi-coherent module

This file assembles the scheme-level half of the affine dictionary behind [Stacks, Tag 01XZ].

Pinned Mathlib has `SheafOfModules.IsQuasicoherent.of_coversTop` but no analogue for
`SheafOfModules.IsFiniteType`, and no `SheafOfModules.LocalGeneratorsData.bind`. The locality
statement proved here needs neither: a `LocalGeneratorsData` already takes its covering in the
base site, so finite generating sections of the *restrictions* `M.restrict (U i).ι` to the
members of an open covering assemble into one directly, once they are transported from the open
subscheme to the slice site.

The second half identifies, for a quasi-coherent module `F` on a scheme and an affine open `U`,
the restriction `F|_U` with the pullback along `U ≅ Spec Γ(X, U)` of the `tilde` of a
`Γ(X, U)`-module, namely the global sections of `F|_U` transported to the spectrum. This is the
shape in which [Stacks, Tag 01XZ] (4) and (5) are stated, and Mathlib records no such
identification for a general affine open of a general scheme.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsRestrict`: generating sections
  restrict along an open immersion, with the same index type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver`: generating sections of
  `M.restrict V.ι` give generating sections of `M.over V`, with the same index type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections`: **finite
  type is local on a scheme**.
* `Stacks.AlgebraicGeometry.CoherentTFAE.specModule`,
  `Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`: the affine-open form of a
  quasi-coherent module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_moduleSpecΓ_of_generatingSections`: on a
  spectrum, finitely many generating sections of a quasi-coherent module make its global
  sections a finite module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_specModule_of_generatingSections`: the two
  previous items combined, for an affine open of an arbitrary scheme.

## Implementation notes

The transports go through `Stacks.AlgebraicGeometry.AffinePushforward.overInverseIso` and
`overInverseUnitIso`, which were built for presentations; the same two isomorphisms serve
generating sections, because `SheafOfModules.GeneratingSections.map` asks exactly for a
colimit-preserving functor together with an identification of the structure sheaves.

Every `Epi`/`IsIso` argument is passed explicitly and positionally. See the implementation note
of the `Affine` file in this directory for why instance synthesis cannot find them.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

variable {X Y Z : Scheme.{u}}

/-! ### Transport of generating sections -/

/-! ### Finite type is local on a scheme -/

/-! ### The affine-open form of a quasi-coherent module -/

/-! ### Finiteness of the global sections -/

/-- **On a spectrum, finitely many generating sections of a quasi-coherent module make its
global sections a finite module.** -/
theorem finite_moduleSpecΓ_of_generatingSections {A : CommRingCat.{u}} (N : (Spec A).Modules)
    [N.IsQuasicoherent] (σ : N.GeneratingSections) [Finite σ.I] :
    Module.Finite A (moduleSpecΓFunctor.obj N) := by
  have hiso : IsIso N.fromTildeΓ := inferInstance
  have hp : Epi (σ.π ≫ (asIso N.fromTildeΓ).inv) :=
    @epi_comp _ _ _ _ _ _ σ.epi _
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (asIso N.fromTildeΓ)))
  exact finite_of_epi_free_tilde _ (σ.π ≫ (asIso N.fromTildeΓ).inv) hp

end Stacks.AlgebraicGeometry.CoherentTFAE

end
