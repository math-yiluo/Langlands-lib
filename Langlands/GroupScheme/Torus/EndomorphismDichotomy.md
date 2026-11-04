# Torus endomorphism dichotomy

Author: Worker 1369.

The theorem `Langlands.GroupScheme.torusEndomorphismDichotomy.{u}` proves the
existing `TorusEndomorphismDichotomyStatement.{u}`. For every algebraically closed
field in arbitrary universe `u`, an endomorphism of an actual torus is surjective
on its underlying scheme or annihilates an actual closed copy of `Gm`.
There is no added splitting, character-duality, or structural-theorem premise.
This module is a prerequisite for the Borel normalizer argument; it does not
prove `BorelNormalizerStatement`.

## Integer lattice argument

`TorusEndomorphism.exists_surjective_annihilator` starts with a noninjective
integer-linear endomorphism `f` of `I → ℤ`, for finite `I`. It constructs a
surjective linear functional `q : (I → ℤ) →ₗ[ℤ] ℤ` satisfying `q (f x) = 0`
for every `x`.

The proof takes a Smith normal form of `LinearMap.range f`, with respect to the
usual basis of `I → ℤ`. If the resulting embedding of the image-basis indices
into the ambient-basis indices were surjective, it would be an equivalence.
The corresponding basis equivalence would identify the source lattice with the
image. Orzech's theorem, applied to this injective equivalence and the
surjective map `f.rangeRestrict`, would make `f.rangeRestrict` injective, and
therefore make `f` injective. This contradicts the premise. A missing ambient
coordinate consequently exists. Its basis coordinate functional vanishes on
the image and takes `z • b i` to every prescribed integer `z`, proving both
annihilation and surjectivity. This argument includes the empty index type:
noninjectivity cannot occur in rank zero.

## Actual diagonalizable morphisms

`Diagonalizable.isClosedImmersion_restrictMap` proves that a surjective
exponent-group map induces a closed immersion of actual diagonalizable group
schemes. The existing `incl_surjective` theorem makes the corresponding map of
group algebras surjective. The existing formula for the underlying scheme map
then reduces the assertion to the closed immersion of spectra of a surjective
ring map.

`Diagonalizable.restrictMap_comp_eq_zero` proves that if `g (h l) = 0` for every
exponent `l`, the composite `D(N) → D(M) → D(L)` induced by `g : M →+ N` and
`h : L →+ M` is the zero homomorphism. It compares points over every relative
test scheme through `Corepresented.pointsEquiv`. The two restriction formulas
reduce character evaluation to evaluation at the zero exponent, hence to the
identity unit. Injectivity of the point equivalence and the existing
all-test homomorphism extensionality theorem give equality of actual morphisms.
The conclusion therefore applies to nonreduced test schemes as well.

## Standard split torus

`TorusEndomorphism.split_surjective_or_closedGm` applies the preceding arguments
to the existing integral `splitTorus.characterMap` of an actual endomorphism of
the standard split torus. The published `diagonalizableMap_splitIso` equality
identifies this actual morphism with the diagonalizable restriction map, up to
the explicit split-torus isomorphism.

If the character map is injective, the existing
`Diagonalizable.flat_and_surjective_restrictMap` theorem gives scheme
surjectivity of the diagonalizable morphism. Conjugation by the explicit
isomorphism gives scheme surjectivity of the original endomorphism.

Otherwise, the lattice lemma supplies a surjective annihilator `q`. The map
sending `m` to the constant function with value `q m` is a surjection onto
`PUnit → ℤ`. It induces a closed immersion from `D(PUnit → ℤ)` into
`D(I → ℤ)`. The existing rank-one split-torus isomorphism and diagonalizable
split isomorphisms turn this into an actual cocharacter `ν : Gm → Gm^I`.
Closed immersion is preserved by these isomorphisms. The zero-composite lemma,
together with `diagonalizableMap_splitIso`, proves `ν ≫ f = 0` as an equality
of commutative group-scheme homomorphisms.

## Arbitrary torus over an algebraically closed field

The final theorem uses the published unconditional
`Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning` theorem through
`SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites`. Algebraic
closedness supplies separable closedness, so this constructs an isomorphism
from the given torus to a standard split torus. Conjugating the endomorphism
allows the split dichotomy to apply. The proof transports scheme surjectivity
back through the isomorphism in the first case. In the second case it composes
the constructed closed cocharacter with the inverse isomorphism and verifies
the zero composite by the isomorphism identities.

Surjectivity here is `AlgebraicGeometry.Surjective` of the actual underlying
scheme map. The second conclusion is exactly the existing
`IsClosedSubgroup (CommGroupScheme.groupHom ν)` and `ν ≫ f = 0`. The argument
makes no claim that the entire kernel is smooth, connected, or a torus, and
uses no restriction on characteristic.

## Chosen closed kernel subgroup

`TorusEndomorphism.kernelGm` is the data-valued construction exported for the
Borel normalizer consumer. Given the actual torus, its torus predicate, an
endomorphism, and the failure of scheme surjectivity, it uses the exact
dichotomy to choose an actual cocharacter. Its subtype records both the closed
immersion and the exact zero composite. Thus its value is a specified actual
closed copy of `Gm` inside the kernel, with both proofs retained.

## Provenance

This is an internal derivation from the existing Library's character-map,
diagonalizable-group, splitting, and all-test point APIs and Mathlib's Smith
normal form and Orzech theorem. The proof route above describes the implemented
Lean argument. The original-source provenance of the target proposition is
recorded in its unchanged `EndomorphismDichotomyStatement.md`; no new literature
claim is introduced here.
