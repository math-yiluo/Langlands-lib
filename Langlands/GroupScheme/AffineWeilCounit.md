# The counit and unit of actual affine Weil restriction on test schemes

Author: Worker 207.

This supporting module works with an arbitrary ring map `A → B`. It writes
`tensorTest A B T = Spec (B ⊗[A] Γ(T))` for the published extension-base test
of a ground-base test `T`. It also writes `groundTest A B Z` for an
extension-base test `Z → Spec B` regarded over `Spec A`. It constructs the two
adjunction-type maps that connect these operations. These are the maps the
converse half of the Weil-restriction dynamics needs. Everything is internal
to the Library: there is no new external assertion and no citation beyond the
standard construction of Weil restriction.

## Affinization

- `algSpec_hom_ext`: two maps into a relative spectrum `Spec C` agree when
  they pull back every global function of `Spec C` to the same function.
- `affinization T : T → Spec Γ(T)` is the unit of the published global
  sections/relative spectrum adjunction `algΓAlgSpecAdjunction`.
  `affinization_appTop` states that it pulls the spectrum coordinate of a
  global function back to that function.
- `gmAffine x` is a multiplicative point of `Spec Γ(T)` attached to a point
  `x : T → 𝔾_m`. `affinization_gmAffine` shows that `x` factors as
  `affinization T ≫ gmAffine x`. Thus every `𝔾_m`-point comes from a standard
  affine test `Spec C`.
- `algebraMap_algSpec` and `algebraMap_groundTest` identify the structure maps
  of a relative spectrum and of a ground test on global functions.

## Counit

For `Z` over `Spec B`, `counitAlgebraMap` is the multiplication
`B ⊗[A] Γ(Z) → Γ(Z)`, `b ⊗ s ↦ b·s` (`counitAlgebraMap_tmul`). The counit
`counit A B Z : Z → tensorTest A B (groundTest A B Z)` is its adjoint map of
`B`-schemes. Proved properties:

- `counit_appTop`, `counit_appTop_includeSection`: the counit pulls back
  coordinates by the multiplication map. In particular it pulls back each
  included ground function `1 ⊗ r` to `r`.
- `counitAlgebraMap_naturality` and `counit_naturality`: the counit is
  natural in `Z` for the published `tensorTestMap`.

## Unit on standard tests

For an `A`-algebra `C`, `standardTest A C = Spec C` over `Spec A`.
`testUnitAlgebraMap` is the right-factor inclusion `C → B ⊗[A] C` (composed
with `Γ(Spec C) ≅ C`). `testUnit A B C : groundTest (tensorTest (Spec C)) →
Spec C` is its adjoint `A`-morphism. `testUnit_appTop` says that it pulls each
function `s` back to `1 ⊗ s`. The triangle identity
`counit_tensorTestMap_testUnit` states
`counit ≫ tensorTestMap (testUnit A B C) = 𝟙`. It is proved on coordinates by
induction over pure tensors.

The unit is constructed only on standard affine tests. That suffices, since
the representing objects of the dynamic subgroups and `𝔾_m` are affine.

## Scalar points

For `Z` over `Spec B`, `lineRestrict` and `gmRestrict` regard an affine-line
point or a multiplicative point of `Z` over `Spec B` as one of `groundTest Z`
over `Spec A`. They use the same global function. Their lemmas cover the
point equivalence, naturality, the zero section, the inclusion
`𝔾_m → 𝔸¹`, and multiplicativity (`gmRestrict_mul`, `gmRestrict_one`).
Combined with the published scalar points of `AffineWeilTorusAdjunction`:

- `counit_scalarLinePoint`, `counit_scalarGmPoints`: the counit followed by
  the scalar point of a restricted point recovers the original point.
- `gmRestrict_scalarGmPoints`: on a standard test, restricting the scalar
  point of `x : Spec C → 𝔾_m` gives `testUnit A B C ≫ x`.
