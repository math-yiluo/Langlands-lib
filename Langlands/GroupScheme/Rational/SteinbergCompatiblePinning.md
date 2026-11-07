# Galois-compatible repinning and normalized simple-root maps

This internal construction combines published actual Lie-weight transport,
Hilbert 90 coordinates on weight lines, supplied split pinnings, existence of
normalized root parametrizations, and fixed-pinning uniqueness. It constructs
compatible vectors and whole root maps under the displayed geometric inputs.
It introduces no additional external structure theorem.

Let `k` and `K` be fields in arbitrary universe `u`, with `K` a finite
extension of `k`. Let `G/k` be an actual affine group scheme and let `p` be
a split pinning of its actual base change `G_K`. Thus the supplied pinning
already includes an actual split maximal torus, its inclusion, a finite
reduced root datum realized by that inclusion, a root-system base, and linear
trivializations of the actual simple-root Lie weight spaces.

The remaining inputs are a commutative group scheme `T/k`, a morphism
`j : T.toGrp ⟶ G`, an isomorphism `eT : p.torus ≅ T_K`, and the square

```
p.inclusion = CommGroupScheme.groupHom eT.hom ≫ j_K.
```

Supply also a homomorphism `rho : Aut_k(K) →* Perm(p.base.support)` satisfying
for every automorphism `sigma` and simple index `a` the actual character law

```
congr eT (p.rootDatum.root (rho sigma a))
  = galoisRepresentation k K T sigma (congr eT (p.rootDatum.root a)).
```

Here `congr eT` precomposes a character by `eT.inv`, and the character
Galois representation is the published ordinary coefficient action. No
compatible root vector or compatible root-map family is supplied. The finite
extension need not be Galois, and neither field is required to be infinite
or perfect.

`SplitPinning.galoisCompatibleRootPinning` chooses actual linear
trivializations of all simple-root weight spaces for which
`galoisCompatibleRootPinning_galois` proves

```
Lie.baseChangeGaloisEquiv k K G sigma (q.rootVector a)
  = q.rootVector (rho sigma a).
```

`SplitPinning.galoisCompatibleRepinning` replaces the `pinning` field of
`p` by these trivializations. Its actual torus, inclusion, root index,
root datum and base are definitionally those of `p`.
`galoisCompatibleRepinning_rootVectors` proves the existing
`RootVectorsGaloisCompatible` proposition for this constructed split
pinning and the same supplied index action.

`SplitPinning.galoisCompatibleRootParametrizations` then chooses normalized
parametrizations for every simple root of the constructed repinning, using
`nonempty_normalizedRootParametrization` from the published
`Rational.NormalizedRootExistenceProof` module. These are actual morphisms
from the one-dimensional vector group representing the whole intrinsic root
subgroup, with the full torus-equivariance law and the prescribed actual
Lie differential. Finally,
`galoisCompatibleRootParametrizations_compatible` proves the existing
`RootMapsGaloisCompatible` proposition. Applying `sigma` to the coefficients
of the entire polynomial root curve, while fixing its variable, gives the
curve at `rho sigma a`. The published uniqueness and all-test descent
argument used for this last step applies to arbitrary scheme tests, including
nonreduced tests; it is not inferred from equality of field-valued points.

The implemented proof first identifies the actual weight space of
`p.inclusion` at any character with that of `j_K` at the character transported
by `eT`. It specializes `weightSpace_map_of_transport` to the identity ambient
isomorphism and proves that its actual Lie differential is the identity.
The published `RelativeRoot.galois_mem_actionWeightSpace`, together with the
conjugation-action comparison and the supplied character law, then transports
each actual simple-root weight space to the space indexed by `rho sigma a`.

For one simple index `a`, restrict to its stabilizer for the supplied action.
The character law shows that this subgroup fixes the corresponding character
of `T_K`. The original pinning trivialization proves that the actual weight
space has dimension one. The published
`RelativeRoot.exists_fixedWeight_equivariant_coordinates` supplies a linear
coordinate compatible with this subgroup's canonical semilinear action.
Its value at `1` is therefore a nonzero actual weight vector fixed by the
entire index stabilizer.

A private generic group-action lemma extends such vectors to all indices.
Choose one stabilizer-fixed vector on each orbit-quotient representative and
transport it to every index. Two transports differ by an element fixing the
representative, so they give the same vector. This proves equivariance under
every group element. Weight membership and nonvanishing are preserved by
the actual semilinear action, so the resulting family consists of nonzero
vectors in the required actual weight spaces. A private linear-algebra
construction makes scalar multiplication by each vector into a linear
equivalence, using the original trivialization to establish dimension one.
Those equivalences form the new root pinning. The final whole-map law is
an application of the published
`rootMapsGaloisCompatible_of_rootVectors` theorem.

The supplied split pinning, descended-torus square, and character-compatible
simple-root action remain inputs. This unit does not construct these data
from quasi-splitness, classify Galois orbits or prove their orthogonality,
construct Steinberg's cross-section or its even-type-A substitutes, or prove
the parent class-quotient theorem. In particular, it asserts no global
rational section of the quotient map.
