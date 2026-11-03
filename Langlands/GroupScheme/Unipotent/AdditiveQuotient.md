# Represented fppf additive quotients

Worker 1448. This is an internal derived construction from the published
coordinate, geometric-integrality and dominant-homomorphism results.

For an arbitrary field `k : Type u` and an actual smooth connected affine
group scheme `U` over `Spec k`, assume the existing fixed-vector predicate
`IsUnipotent U` and the nontriviality condition
`SubgroupFunctor.range (𝟙 U) ≠ ⊥`. Then
`exists_additive_fppf_quotient` constructs a nonzero homomorphism

`q : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1`

and proves `RelativeRoot.IsFppfQuotient
(SubgroupFunctor.range (kernelι q)) q`. Thus the actual scheme map is flat,
surjective and locally of finite presentation, and its specified subgroup
is its actual scheme kernel on every test. Scheme surjectivity does not
assert surjectivity on the group of points of each original test scheme.
No perfectness or characteristic restriction is used.

`additiveFppfQuotient` is the noncomputable chosen construction: its value
is a morphism together with proofs of nonvanishing and the full stated
fppf quotient property.

## Implemented argument

In an augmented domain over a field, a nonzero element killed by the
augmentation is transcendental. Indeed, a nonzero algebraic element would
be a unit, and its image under the augmentation could not be zero.
`transcendental_of_augmentation_eq_zero` proves this general algebraic fact.

A primitive coordinate has augmentation zero. Algebraic independence of
its singleton family makes the corresponding polynomial evaluation map
injective. Its kernel is therefore contained in the nilradical, so the
map of prime spectra has dense range. The previously constructed
primitive-family morphism has exactly this spectrum map as its underlying
scheme morphism. This proves `isDominant_quotientMap_of_isPrimitiveElem`.

`isDomain_of_smooth_connected` uses `smoothConnectedAffineGeometry` to
make a smooth connected corepresented affine group geometrically integral.
Over the spectrum of a field this makes the group integral, and the
affine integrality criterion makes its coordinate algebra a domain.

For a nonzero primitive coordinate on a corepresented group whose
coordinate algebra is a domain and whose structure map is locally of
finite type, `isFppfQuotient_quotientMap_of_isPrimitiveElem` applies the
published `DominantHomFlat.flat_of_isDominant`. The source and target are
affine, giving quasi-compactness; finite type of the structure map gives
finite type of the homomorphism. The target Ga is reduced, irreducible
and locally noetherian. `DominantHomFlat.surjective_of_flat` then gives
surjectivity, and the noetherian finite-type criterion gives local finite
presentation.

For the smooth connected unipotent application, nontriviality supplies a
nonconstant coordinate by the earlier all-test constant-coordinate
triviality criterion. The earlier primitive-coordinate construction
produces a nonzero primitive element. The preceding arguments give its
fppf property, and the universal-point argument from `AdditiveCharacter`
proves nonvanishing. Finally, the affine coordinate group isomorphism
transports smoothness, connectedness, unipotence, nontriviality and the
fppf quotient back to the original group scheme.

## Scope

This construction proves neither smoothness nor connectedness of the
kernel of the chosen quotient. It does not yet construct a finite
represented Ga-series and does not prove
`PerfectFieldUnipotentSplitStatement` or
`AlgebraicallyClosedSplitSolvableStatement`. The trivial group is excluded
only from this intermediate nonzero-quotient construction.
