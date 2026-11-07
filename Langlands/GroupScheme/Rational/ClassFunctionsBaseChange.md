# Field base change for the actual class-function algebra and quotient

Author: Worker 1729.

This module proves
`Langlands.GroupScheme.ClassFunctions.fieldBaseChange : FieldBaseChangeStatement.{u}`
from `Langlands.GroupScheme.Rational.ClassFunctionsBaseChangeStatement`.
For arbitrary fields `K F : Type u`, an algebra structure `[Algebra K F]`,
and an affine actual group scheme `G` over `Spec K`, it constructs the ambient
coordinate equivalence, the invariant-algebra equivalence and the isomorphism
of the actual canonical affine quotients, with all four equations of that
published proposition. Affineness after base change follows from stability
under pullback. No further geometric or comparison hypothesis is used.

Write `b = algebraBaseMap K F`, `GF = (GroupScheme.baseChange b).obj G`,
`C = Coord G`, `CF = Coord GF`, and `I = algebra G`. All helper declarations
below lie in `Langlands.GroupScheme.ClassFunctions.BaseChange`.

## Actual ambient coordinates

`presentation` makes `Descent.TensorCoordinates.baseChangeIso` into an
isomorphism over `Spec F` from the spectrum of `F ⊗[K] C` to the actual
pullback underlying `GF`. Composing its inverse with `Lie.coordinateIso GF`
gives an isomorphism between two relative spectra. Full faithfulness of
`algSpec`, followed by passage from an isomorphism of commutative algebras
to an algebra equivalence, defines

```lean
e = coordinates K F G : (F ⊗[K] C) ≃ₐ[F] CF
```

`coordinates_spec` identifies its spectrum over `Spec F`.
`coordinates_spec_left` takes the underlying scheme maps and proves precisely
the first equation of the target.

The map `restriction : C →ₐ[K] CF` is the inclusion of the right tensor factor
followed by `e`, with scalars restricted to `K`. The identity
`restriction_spec` says that its spectrum is the first projection of the
actual pullback, in the chosen coordinate presentations. Consequently,
`point_restriction` identifies composition with this algebra map with
`Lie.affineBaseChangeEquiv K F G A` for every commutative coefficient algebra
`A` over `F` with the compatible `K`-algebra structure. This uses the actual
pullback equivalence of affine points, which is multiplicative; it does not
assume a comparison for the conjugation action.

## Conjugation and the equalizer

`squareCoordinates` is the tensor reassociation and scalar-cancellation
isomorphism followed by the tensor product of `e` with itself. It has type

```lean
(F ⊗[K] (C ⊗[K] C)) ≃ₐ[F] (CF ⊗[F] CF)
```

Its formula on pure tensors is
`c ⊗ (a ⊗ d) ↦ e (c ⊗ a) ⊗ e (1 ⊗ d)`, proved in
`squareCoordinates_tmul`. After restriction to the original tensor square,
`square_restriction` identifies it with `tensorEvaluation` at the two actual
restricted universal points of `GF`.

`conjugation_coordinates` now compares the scalar extension of
`conjugationPullback G` with `conjugationPullback GF`. Its proof applies
`evaluate_conjugationPullback` to those points and uses the multiplicativity
of `Lie.affineBaseChangeEquiv`, including preservation of inverses, followed
by `point_restriction`. Thus the comparison concerns the conjugation of the
actual group schemes. `right_coordinates` proves the matching identity for
the second-factor inclusion by the pure-tensor formula.

The helper `tensorAlgebra` is the equalizer of these two scalar-extended
maps inside `F ⊗[K] C`. By the two comparisons and injectivity of
`squareCoordinates`, `mem_tensorAlgebra` proves

```lean
x ∈ tensorAlgebra K F G ↔ coordinates K F G x ∈ algebra GF
```

The restriction of `e` and its inverse therefore defines
`equalizerCoordinates : tensorAlgebra K F G ≃ₐ[F] algebra GF`.

Every module over the field `K` is flat. Mathlib's
`AlgHom.tensorEqualizerEquiv F F (conjugationPullback G) (includeRight G)`
therefore identifies `F ⊗[K] I` with `tensorAlgebra K F G`. Composing with
`equalizerCoordinates` defines

```lean
phi = invariants K F G : (F ⊗[K] algebra G) ≃ₐ[F] algebra GF
```

`AlgHom.tensorEqualizerEquiv_apply` and `AlgHom.coe_tensorEqualizer` identify
the inclusion of this equivalence into the ambient tensor algebra.
`invariants_inclusion` then proves exactly the target's second equation:

```lean
e.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id F F) (inclusion G)) =
  (inclusion GF).comp phi.toAlgHom
```

The use of flatness is solely to identify the equalizer after scalar extension.
The actual class-function algebra remains the published literal equalizer
throughout; no replacement by invariance on field-valued points is made.

## The canonical quotient and its map

For a commutative `K`-algebra `D`, `scalarSpec K F D` lifts
`HopfMorphismBaseChange.tensorSpecIso K F D` to an isomorphism over `Spec F`.
`scalarSpec_naturality` derives its compatibility with every `K`-algebra
homomorphism from `HopfMorphismBaseChange.tensorSpecIso_naturality` by
composing with the appropriate tensor-spectrum isomorphism. `presentation_eq`
relates this comparison to the earlier actual coordinate presentation.

`quotientComparison` is `scalarSpec K F (algebra G)` followed by relative Spec
of `phi.symm`. Its source is `(Over.pullback b).obj (quotient G)` and its
target is the actual published `quotient GF`. By construction,
`quotientComparison_left` proves the target's third equation:

```lean
(quotientComparison K F G).hom.left =
  (HopfMorphismBaseChange.tensorSpecIso K F (algebra G)).hom ≫
    Spec.map (CommRingCat.ofHom phi.symm.toRingHom)
```

Finally, `quotientComparison_rho` proves the fourth equation in the over
category. It precomposes with the isomorphism `(Lie.coordinateIso GF).hom`,
rewrites it using `coordinates_spec` and `presentation_eq`, and unfolds the
published definition of `rho`. Functoriality cancels the original coordinate
isomorphism. Spectrum naturality moves the tensor comparison past the
inclusion, and `invariants_inclusion`, composed with `phi.symm`, identifies
the resulting algebra map with `inclusion GF`. Cancellation of the initial
coordinate isomorphism yields

```lean
(Over.pullback b).map (rho G) ≫ (quotientComparison K F G).hom = rho GF
```

The final theorem supplies `coordinates`, `invariants`, and
`quotientComparison`, together with these four identities, directly to the
existential conclusion of `FieldBaseChangeStatement.{u}`.

## Provenance and scope

Provenance: derived/internal. This is an affine-coordinate and flat-equalizer
proof of the published internal proposition. The imported actual-point
comparison is `Lie.affineBaseChangeEquiv` in
`Langlands.GroupScheme.Lie.BaseChange`; the flat equalizer API is in the pinned
`Mathlib.RingTheory.Flat.Equalizer`. Spectrum comparison uses the published
`Descent.TensorCoordinates` and `HopfMorphismBaseChange` APIs. No external
literature assertion is used as an unproved input to this module.

The result has arbitrary universe `u` and arbitrary fields `K` and `F` with
the given algebra structure. The only geometric assumption is affineness of
`G.X.hom`. All three comparisons and all four compatibility equations are
constructed conclusions. The result asserts base change of the canonical
invariant algebra and its spectrum; it makes no finite-generation,
geometric-fibre, cross-section, or rational-lifting claim. The target pair,
its imports, and the quasi-split Steinberg quotient statement and its imports
are unchanged.
