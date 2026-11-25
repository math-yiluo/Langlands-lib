module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Local criteria for a morphism of modules to be invertible, and inverse images

This file collects the three facts about sheaves of modules on schemes that the base-change
assertion of Stacks Tag 02KG is proved from: that invertibility is local on the scheme, that
on an affine scheme invertibility of a morphism of quasi-coherent modules is detected on
global sections, and that the inverse image of a quasi-coherent module is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` and
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`: a morphism of sheaves
  of modules which is invertible on every stalk, respectively whose restriction to each member
  of an open covering is invertible, is invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`: on an affine scheme
  a morphism of quasi-coherent modules which is invertible on global sections is invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`: the inverse image of a
  quasi-coherent module along an arbitrary morphism of schemes is quasi-coherent.  This is
  Stacks Tag 01BG; the affine case `isQuasicoherent_pullback_of_isAffine` is reduced to
  `Stacks.AlgebraicGeometry.SectionsColimit.isQuasicoherent_pullback_specMap` by conjugating
  with `AlgebraicGeometry.Scheme.isoSpec`.

## Implementation notes

`isIso_of_isIso_stalk` is Mathlib's `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` for the
underlying sheaf of abelian groups, combined with the fact that
`AlgebraicGeometry.Scheme.Modules.toPresheaf` reflects isomorphisms.  Locality is then
obtained from `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, which identifies the
stalks of a restriction with the stalks of the original module.

`isIso_of_isIso_moduleSpecΓ` is the naturality of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` together with
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`, which makes the components of that
natural transformation invertible at quasi-coherent modules.

For `isQuasicoherent_pullback` the covering used is the one produced by
`TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le` from the affine opens of the source
and the preimages of the affine opens of the target: over such a member `U`, lying over an
affine open `V`, the morphism factors as `U.ι ≫ f = f.resLE V U _ ≫ V.ι`, so the restriction
of `f ^* F` to `U` is an inverse image of `F.restrict V.ι` along a morphism of affine schemes.

Several `IsIso` instances below are supplied by explicit application of
`CategoryTheory.IsIso.comp_isIso` rather than by `infer_instance`: the category structure on
`AlgebraicGeometry.Scheme.Modules` is a different instance from the one on `SheafOfModules`,
equal to it only after unfolding a non-reducible definition, and instance search does not see
through that.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-! ### Invertibility is local -/

/-! ### The affine criterion -/

/-! ### Quasi-coherence of the inverse image -/

/-- The inverse image of a quasi-coherent module along an open immersion is quasi-coherent. -/
theorem isQuasicoherent_pullback_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : Y.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N) inferInstance

end Stacks.AlgebraicGeometry.AffineBaseChange

end
