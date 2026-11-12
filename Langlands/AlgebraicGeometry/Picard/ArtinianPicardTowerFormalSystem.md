# A formal system from the actual Picard source tower

The definition
`PicardGroupoid.ArtinianPicardTowerFormalSystem.system`
constructs an actual `FormalLineBundleSystem` over the unchanged published
`ArtinianPicardSourceTower.limitRing`.

Its inputs are a commutative base ring `k`, a field `K` with `Algebra k K`,
a commutative Noetherian local `k`-algebra `R` complete for its maximal ideal,
a surjective `k`-algebra map `ε : R →ₐ[k] K`, a proper flat morphism
`f : X ⟶ Spec k`, an actual line bundle `M` on its relative `K`-fibre,
and an initial `ArtinianPicardSourceStep.Stage ε f M`. Write `C` for the
published limit ring of this source tower and `mC` for its maximal ideal.
The output is a formal system for
`ArtinianFormalPicardFamily.totalMap (R := C) f` and `mC`.
There is no finite-type assumption on `k`, `R` or `K` in this construction.

The published ideal-cofinality proof supplies, at every adic level, a tower
stage whose projection kernel is contained in the corresponding power of the
limiting maximal ideal. Taking successive maxima makes the chosen stage
indices increasing. The existing `toAdic` maps then give actual augmented
maps from these selected tower stages to the ordinary adic tests.
`towerMap_toAdic` and `toAdic_adicTransition` prove the adjacent commutative
square. Pullback of the existing tower bundle transitions along this square
provides actual bundle isomorphisms between consecutive relative adic tests.

The final definition transfers these bundles to the ordinary scheme
thickenings used by `FormalLineBundleSystem`. The map to the original
relative space is constructed by the actual pullback universal property.
Its compatibility with the adic transitions follows by checking both
projections. Ordinary line-bundle pullback composition transports the bundle
isomorphisms along those maps.

The provenance is internal: this assembles existing published tower,
cofinality and pullback constructions. All scalar maps, quotient rings and
scheme fibre products retain their given common arbitrary universe. The
formal-system type requires adjacent isomorphisms only; no coherence or
residue-compatibility law for the independently chosen `transitionIso` is
used or claimed. Source existence, formal versality and the final
`FiniteTypeFormalVersalBundleStatement` remain separate proof obligations.
