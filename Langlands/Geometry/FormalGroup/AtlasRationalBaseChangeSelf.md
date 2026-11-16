# Naturality of the actual identity coefficient comparison

This is internal infrastructure derived from `AtlasBaseChangeSelf`,
`AtlasBaseChangeAlong` and the global tensor constructions in
`AtlasRationalMorphism` and `AtlasRationalBaseChangeAlong`. It makes no new
original-literature assertion.

Let `O` be a commutative ring, `R` a commutative `O`-algebra and `F` a field
with an `O`-algebra structure. Coordinate types are finite and may differ.
Tests have the universe of `R`. An integral or rational map has equal original
principal-open covers. Rational Hom means the global finite tensor
`F ⊗[O] BasicAtlas.Hom`, with actual formal, coefficient-natural chart maps in
the integral factor.

`baseAlongMapOpens_eq` gives the equality of image covers for any supplied
coefficient algebra homomorphism. Its displayed type uses the transported
atlases over the supplied target scalar structure.

`Hom.baseId_natural` proves the forward naturality square for the existing
actual identity comparison:

```text
Y.baseIdHom ∘ (f extended along id) = f ∘ X.baseIdHom.
```

The chart calculation removes the identity-coordinate comparisons, uses
coefficient naturality along `identityTestHom`, then identifies the selected
preimage generator with the original one using `baseIdSource_eq`.
`Hom.baseId_inv_natural` proves the reverse square using this equation,
associativity and the two inverse equations of the actual `baseIdIso`.

`RationalHom.baseId_natural` and `baseId_inv_natural` prove the same two
equations for every global rational map, using the rationalizations of the
integral comparisons. Tensor induction reduces sums by additivity and pure
tensors to scalar multiples of integral rationalizations. Linearity of
coefficient extension, bilinearity of composition and the integral equations
then close the proof. Neither injectivity of integral rationalization nor
detection of a global tensor by chart evaluation is assumed.

With the additional assumptions `IsDomain O` and `IsFractionRing O F`,
`baseIdQuasiIsogeny X` rationalizes both maps of the existing actual
`X.baseIdIso`; its two inverse equations come from `QuasiIsogeny.ofIso`.
The `hom` and `inv` projection lemmas identify its maps with the
rationalizations of `baseIdHom` and `baseIdInv`.
`QuasiIsogeny.baseId_natural` and `baseId_inv_natural` give the two corresponding
quasi-isogeny squares. Equality follows from the forward rational map
equation and the existing uniqueness of a two-sided inverse.

These are naturality laws for the specified identity comparison, not strict
equalities of atlases or independence of arbitrary comparison choices. The
module does not assert successive-extension coherence, local rational
gluing, full-order equivariance, heights, framing, polarization, descent,
levels or representability.
