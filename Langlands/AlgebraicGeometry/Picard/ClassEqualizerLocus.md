# The locus where two fppf Picard classes agree, as a sieve on a scheme

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Picard.ClassEqualizerLocus`. It
imports the Library modules
`Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer`
(`AlgebraicSpace.RepresentsEqualizer`) and
`Langlands.AlgebraicGeometry.Picard.RelativePicardLocalRepresentatives`
(`RelativePicard.isomorphismSieve`,
`RelativePicard.sheafClassOf_eq_iff_isomorphismSieve_mem` and, through its
imports, the relative Picard presheaf and its fppf sheafification), together
with Mathlib's `CategoryTheory.Sites.Closed` (closure of a sieve for a
Grothendieck topology).

## Purpose and provenance

This is an internal helper for the diagonal branch of the proof of
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement`.
There one must find, for line bundles `L` and `M` on `T ×_S X`, a morphism of
schemes `ι : Z ⟶ T` through which a test morphism factors exactly when the
fppf Picard classes of `L` and `M` agree after restriction along it. This
module reduces that task to a question about one sieve on the scheme `T`. No
literature theorem is claimed. The facts proved here are formal consequences of
the Library's description of equality of sheafified classes
(`sheafClassOf_eq_iff_isomorphismSieve_mem`), of Mathlib's equivalence
`Sieve.overEquiv` between sieves on an object of `Over S` and sieves on its
underlying scheme, and of the additivity of the class map on line bundles.

## Conventions

- `S X : Scheme`, `f : X ⟶ S`, and `T : Over S`. The relative space
  `(relativeSpace f).obj T` is the fibre product `T ×_S X`.
- For a scheme morphism `g : T' ⟶ T.left`, the test object over `S` is
  `Over.mk (g ≫ T.hom)` and the corresponding morphism of `Over S` is
  `Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T`.
- `classOf f T L` is the class of the line bundle `L` in the Picard group of
  `T ×_S X`, `classPresheaf f` is the presheaf of these groups (as sets), and
  `sheafClassOf f T L` is the image of `classOf f T L` in the fppf
  sheafification `classSheafPresheaf f`.

## Morphisms cutting out a sieve

- `CutsOut ι E`, for `ι : Z ⟶ Y` and a sieve `E` on the scheme `Y`, means that
  a morphism `g : T ⟶ Y` factors through `ι` exactly when `g ∈ E`. The lift is
  not required to be unique.
- `CutsOut.congr_sieve`: the property transports along an equality of sieves.
- `CutsOut.comp`: if every member of `E` factors through `j : W ⟶ Y`, and
  `ι : Z ⟶ W` cuts out the pullback sieve `E.pullback j`, then `ι ≫ j` cuts out
  `E`.
- `CutsOut.pullback`: if `ι₀` cuts out `E₀` on `Y₀` and `φ : Y ⟶ Y₀`, then the
  second projection `pullback.snd ι₀ φ` cuts out `E₀.pullback φ`.

## The isomorphism locus on the underlying scheme

All declarations below are in the namespace `RelativePicard`.

- `isomorphismSieve_pullback`: pulling back the Library's
  `isomorphismSieve f T L M` along `φ : V ⟶ T` gives the isomorphism sieve of
  the pulled-back bundles on `V ×_S X`.
- `isoLocus f T L M : Sieve T.left` is `Sieve.overEquiv T` applied to
  `isomorphismSieve f T L M`.
- `isoLocus_iff`: `g : T' ⟶ T.left` lies in `isoLocus f T L M` exactly when the
  pullbacks of `L` and `M` along `(relativeSpace f).map (Over.homMk g)` are
  isomorphic.
- `isoLocus_pullback`: for `φ : V ⟶ T` in `Over S`, the pullback of
  `isoLocus f T L M` along `φ.left` is the isomorphism locus of the pulled-back
  bundles.
- `isoLocus_congr`: the locus depends only on the isomorphism classes of `L` and
  `M`.
- `isoLocus_eq_tensor_inverse`: the isomorphism locus of `L` and `M` equals the
  isomorphism locus of `L ⊗ M⁻¹` and the trivial bundle. Here `L ⊗ M⁻¹` is
  `LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L
  M.inverse`. The proof uses `classOf_tensor`, `classOf_inverse`,
  `classOf_trivial` and the additivity of pullback on Picard groups.
- `isoLocus_trivial_iff`: `g` lies in the isomorphism locus of `N` and the
  trivial bundle exactly when the pullback of `N` along
  `(relativeSpace f).map (Over.homMk g)` is isomorphic to the trivial bundle.

## Equality of fppf classes

- `map_sheafClassOf_eq_iff`: for `φ : V ⟶ T` in `Over S`, the restrictions
  along `φ` of `sheafClassOf f T L` and `sheafClassOf f T M` are equal exactly
  when `φ.left` lies in the closure `Scheme.fppfTopology.close (isoLocus f T L
  M)`. The proof combines `map_sheafClassOf`,
  `sheafClassOf_eq_iff_isomorphismSieve_mem`, `isomorphismSieve_pullback`,
  Mathlib's `GrothendieckTopology.mem_over_iff` and
  `Sieve.overEquiv_pullback`.
- `representsEqualizer_of_cutsOut`: if a scheme morphism `ι : Z ⟶ T.left` cuts
  out `Scheme.fppfTopology.close (isoLocus f T L M)`, then
  `Over.homMk ι : Over.mk (ι ≫ T.hom) ⟶ T` satisfies
  `AlgebraicSpace.RepresentsEqualizer` for the classes `sheafClassOf f T L` and
  `sheafClassOf f T M` in `classSheafPresheaf f`. A test morphism `φ : V ⟶ T`
  of `Over S` factors through `Over.homMk ι` in `Over S` exactly when `φ.left`
  factors through `ι`, because the structure morphism of the lift is forced.
