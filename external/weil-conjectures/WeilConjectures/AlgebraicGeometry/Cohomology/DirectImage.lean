/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocus
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity

/-!
# Higher direct images, and cohomology and base change

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`; it was split to keep the compilation
of each part cheap.

Let `f : X ⟶ T` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation which is flat over `T`. This module states the fundamental finiteness and
base-change results about the higher direct images `R^q f_* ℱ`.

The higher direct images are the right derived functors of the pushforward functor
`AlgebraicGeometry.Scheme.Modules.pushforward f` between the abelian categories `X.Modules`
and `T.Modules`. This is a different construction from the sheaf cohomology `ℱ.H q` of
`WeilConjectures/AlgebraicGeometry/Cohomology/Defs.lean`, which is an `Ext`-group in abelian
sheaves; `nonempty_sections_higherDirectImage_iso_H` below is the comparison between the two,
and it is what lets the statements of this module be combined with the ones phrased through
`ℱ.H q`.

## Implementation notes

Every derived-functor statement below needs injective resolutions in `X.Modules`, carried as
an instance hypothesis `[HasInjectiveResolutions X.Modules]`. It can be discharged by
`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`, which gives `EnoughInjectives` and
hence `HasInjectiveResolutions`; it is not an instance, so the hypothesis is kept in the
statements here and downstream.

Mathlib has no `IsCoherent` class for sheaves of modules. Over a locally Noetherian base
coherence is equivalent to being quasi-coherent and of finite presentation, so that is what the
statements below use; they should be restated with coherence once it exists.

There is no derived category of `X.Modules` with a derived pushforward available, so "`R f_* ℱ`
is perfect" is stated through an explicit bounded complex of finite free modules whose
cohomology computes the higher direct images after every base change. Base change of `f` and `ℱ`
along `g : T' ⟶ T` is spelled out through an explicit cartesian square `sq : IsPullback g' f' f g`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
and the pullback `ℱ' := (Modules.pullback g').obj ℱ`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.higherDirectImage`: the `q`-th higher direct image
  functor `R^q f_*`, the `q`-th right derived functor of the pushforward.
- `AlgebraicGeometry.Scheme.Modules.IsFlatOver`: flatness of a sheaf of modules over the base
  of a morphism, checked on affine opens.
- `AlgebraicGeometry.Scheme.Modules.hFiber`: the fibre dimension
  `dim_{κ(t)} H^q(X_t, ℱ_t)`.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex`: a cochain complex of finite free
  modules concentrated in degrees `[0, d]`.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`: a family of cohomology sheaves
  is that of a finite locally free module of rank `r` placed in degree `i`.
- `AlgebraicGeometry.Scheme.Modules.perfectLocus` and `perfectLocusOfRank`: the perfect locus
  `U_i` of points where the fibre cohomology vanishes outside degree `i`, and the locus `U_{i,r}`
  where moreover it has dimension `r` in degree `i`.
- `AlgebraicGeometry.Scheme.Modules.eulerCharFiber`: the Euler characteristic of the fibres.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_sections_higherDirectImage_iso_H` and
  `exists_bijective_semilinearMap_sections_higherDirectImage_H`: over an affine base, the global
  sections of `R^q f_* ℱ` are `H^q(X, ℱ)`, linearly over `Γ(T, ⊤)`. Hence
  (`hFiber_eq_finrank_sections_higherDirectImage`) the fibre dimension is the dimension of the
  higher direct image of the fibre to the point; over a field `K`, the sections of `R^q f_* ℱ`
  are `H^q(X, ℱ)` as `K`-vector spaces
  (`nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H`).
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`: the higher direct
  images commute with restriction to an open subscheme of the base.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isAffineHom` and
  `isQuasicoherent_pushforward_of_isAffineHom`: the higher direct images along an affine morphism
  vanish, and its pushforward preserves quasi-coherence.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`: the
  projection formula `R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩` for an invertible `𝒩`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`,
  `exists_isZero_higherDirectImage_restrict` and `exists_isZero_higherDirectImage`: for `f`
  quasi-compact and quasi-separated (resp. separated) and `ℱ` quasi-coherent, the higher direct
  images are quasi-coherent, vanish in large degrees locally on `T`, and vanish uniformly in large
  degrees over a quasi-compact `T`.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`: over any base,
  `R f_* ℱ` is locally given by a bounded complex of finite free modules compatible with base
  change.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`: coherence of the
  higher direct images over a locally Noetherian base.
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_H_of_isProper`: the cohomology of a
  coherent sheaf on a proper scheme over a field is finite-dimensional.
- `AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber` and
  `exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`: semicontinuity of
  the fibre dimension, and Grauert's theorem over a reduced base.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`: the
  locus where a bounded complex of finite free modules is finite locally free of rank `r` in
  degree `i` is open, and characterised by pullbacks.
- `AlgebraicGeometry.Scheme.Modules.exists_forall_hFiber_eq_zero`: locally on `T`, the fibre
  cohomology vanishes in large degrees.
- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le`: openness of the loci `U_{i,≤r}`, and
  hence of the perfect locus `U_i`.
- `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber`: the fibre Euler
  characteristic is locally constant; hence so is the fibre dimension on `U_i`
  (`isLocallyConstant_hFiber_restrict`), and `U_{i,r}` is open (`isOpen_perfectLocusOfRank`,
  `isOpen_setOf_hFiber_eq`).
- `AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`: the fibre dimension is
  invariant under base change.
- `AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback` and
  `isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`: after base change into `U_{i,r}`,
  `R f'_* ℱ'` is finite locally free of rank `r` placed in degree `i`; in particular
  (`isZero_higherDirectImage_restrict` and `isFiniteLocallyFreeOfRank_higherDirectImage_restrict`)
  so is `R f_* ℱ` over an open subscheme contained in `U_{i,r}`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`: after
  base change into `U_i`, `R^i f'_* ℱ' ≅ g^* R^i f_* ℱ`.
- `AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`,
  `range_subset_setOf_hFiber_eq_iff` and
  `exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree`: this shape of `R f'_* ℱ'`
  characterises the morphisms into `U_{i,r}`.
-/
