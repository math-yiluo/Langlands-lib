# Line bundles can be rigidified along a finite morphism near every point

Module `Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedLocal`.

This internal module uses the rigidification framework of
`Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses` (data `f : X ⟶ S`,
`g : Z ⟶ S`, `z : Z ⟶ X`, `hz : z ≫ f = g`, rigidification along
`zRel f g z hz : relativeSpace g ⟶ relativeSpace f`).

`SubschemeRigidification.exists_open_rigidification` assumes only that `g` is finite. For every
test scheme `T : Over S`, every line bundle `L` on `T ×_S X` and every point `t` of `T`, it gives
an open immersion `ι : W ⟶ T` in `Over S` whose image contains `t`, together with a rigidified
class over `W` whose underlying ordinary class is the class of the pullback of `L` to `W ×_S X`.

Proof: choose an affine open `T₀ ∋ t` of `T`. Then `Y = T₀ ×_S Z` is affine and the projection
`p : Y ⟶ T₀` is finite. Let `N` be the pullback of `L` to `Y` along `zRel` (after restricting
`L` to `T₀ ×_S X`). The helper `FinitePointsGeneratingSection.exists_nbhd_le_trivializationOpen` gives an
open `W ∋ t` of `T₀` and a section `σ` of `N` generating it on `p⁻¹(W)`. The relative-space map
`W ×_S Z ⟶ Y` lands in `p⁻¹(W)` by naturality of the relative projection, so
`nonempty_pullback_iso_of_le_trivializationOpen` trivializes the pullback of `N` to `W ×_S Z`.
Composing with the pullback comparisons and the naturality of `zRel` turns this into a
rigidification of the pullback of `L` to `W ×_S X`; its class forgets to the required ordinary
class by definition (`forgetClasses_classOf`).

`OpenSubschemeRigidificationStatement` packages this conclusion, quantified over all schemes
in universe `u` and all finite `g`, and `openSubschemeRigidification` proves it.

Provenance: internal. The statement is the local triviality of line bundles on a finite
`T`-scheme near every point of `T`, which is the standard reason rigidified Picard functors
surject locally onto ordinary ones; the proof uses only the helper module above, the
rigidification framework and Mathlib.
