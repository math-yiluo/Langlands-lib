# Actual complete local polynomial sources for augmented Artinian tests

This internal construction specializes the actual completion comparison in
`AugmentedAdicCompletion` to the actual local polynomial source in
`LocalPolynomialArtinianSource`. The namespace is
`Langlands.AlgebraicGeometry.Deformation.CompletedLocalPolynomialSource`.
All scalar rings, residue fields, variable types and test algebras lie in an
arbitrary common universe `u`.

Let `k` be a commutative noetherian ring, let `K` be a field with its specified
`k`-algebra structure, let `σ` be a finite type, and fix a surjective
`k`-algebra homomorphism

`ε : MvPolynomial σ k →ₐ[k] K`.

The module does not require a `K`-algebra structure on an Artinian test.
In particular, it applies to the actual augmented tests whose specified
surjection to `K` has no `k`-algebra section.

## The actual complete local ring

Write `R = LocalPolynomialArtinianSource.ring ε`. This is the actual
localization of the polynomial ring at `ker ε`, with the specified extension
of `ε` as its residue augmentation. The abbreviation `ring ε` is literally

`AdicCompletion (IsLocalRing.maximalIdeal R) R`.

Finite variables and noetherianness of `k` make `R` noetherian. Mathlib's
`AdicCompletion.LocalRing` instances, imported through
`AugmentedAdicCompletion`, make the completed ring local and adically complete
with respect to its actual maximal ideal. The module's noetherian-ring
instance uses the already published theorem
`AdicCompletion.isNoetherianRing_of_isNoetherianRing` in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing`.
Thus this is an actual complete noetherian local ring.

`sourceMap ε` is the canonical `k`-algebra homomorphism from `R` into this
completion. `polynomialMap ε` composes it with the original polynomial
localization map. `augmentation ε hε` is the residue augmentation constructed
in `AugmentedAdicCompletion`, using the specified surjectivity proof `hε`.
Its surjectivity is `augmentation_surjective`, and the exact triangle

`(augmentation ε hε).comp (polynomialMap ε) = ε`

is `augmentation_polynomialMap`. The two triangle/surjectivity lemmas do not
need finite variables or noetherianness of `k`; those assumptions enter the
complete-local and all-map comparison results.

## Classification of all compatible maps

For every actual `ArtinianTest k K` object `A`, `Maps ε hε A` is the subtype
of all `k`-algebra homomorphisms from the completed ring to `A.algebra`
whose composite with `A.augmentation` equals `augmentation ε hε`.
There is no extra continuity premise or selected class of maps.

`localMapEquiv ε hε A` identifies these maps with all compatible maps from
`R`. Its forward map is restriction along `sourceMap ε`. It is the
general completion equivalence: target maximal-ideal nilpotence makes every
original compatible map factor through a finite quotient; actual completion
projections extend it; approximation to any prescribed order proves
uniqueness for every compatible completed-source map.

Composing this equivalence with the polynomial-source coordinate equivalence
gives `coordinateEquiv ε hε A`. Its target is exactly

`{a : σ → A.algebra // ∀ i, A.augmentation (a i) = ε (MvPolynomial.X i)}`.

`coordinateEquiv_apply` identifies the `i`th coordinate of a map `α` with
`α.val (polynomialMap ε (MvPolynomial.X i))`. Thus the equivalence describes
all maps by their actual polynomial variable values.

`postcomp ε hε q` uses any actual augmented test arrow `q : A ⟶ B`.
`localMapEquiv_naturality` proves that restricting a postcomposed map is the
postcomposition of its restriction.

## Existence and lifting

`maps_nonempty ε hε A` supplies a compatible completed-source map for every
actual test `A`. The proof transports the polynomial-source construction
through `localMapEquiv`: choose preimages of variable residue values in
`A`, extend by the localization universal property, and then extend to
the completion.

`postcomp_surjective ε hε q hq` states that postcomposition is surjective
for every actual test arrow whose underlying algebra map is surjective.
For any completed-source map to `B`, first restrict it to `R`. The original
polynomial-source lifting theorem lifts the variable coordinates to `A`.
Extend the lifted map to the completion. Naturality and injectivity of
`localMapEquiv` prove that its composite with `q` is exactly the given map.
This quantifies every compatible map and every surjective arrow, with no
additional hypothesis on its kernel or on a residue-field section.

## One choice for a finite-type residue algebra

If `K` is a finite-type `k`-algebra, `finiteTypeRing k K` uses the single
surjective finite polynomial presentation chosen in
`LocalPolynomialArtinianSource.finitePresentation k K`.
The chosen variable type is `ULift.{u} (Fin d)`, preserving universe `u`.
This choice gives polynomial generators; no separate finite-relations
claim is required. The same presentation and completed ring are used for
every Artinian test and every test arrow.

`finiteTypeAugmentation k K` is its specified surjective residue
augmentation. `FiniteTypeMaps k K A` contains all maps satisfying the same
residue equation. `finiteType_maps_nonempty` and
`finiteType_postcomp_surjective` specialize the existence and lifting
results to this single actual complete noetherian local source.
For a field base this covers every finite-type residue extension, including
inseparable ones.

## Provenance and retained obligations

This is an internal composition of already constructed algebraic universal
properties, the actual completion comparison, and the published noetherian
completion theorem. No external geometric assertion is used.
The completed ring is an ambient algebra source for augmented tests. This
module constructs no Picard object, versal deformation or hull, formal
Picard family, algebraization, or smooth scheme atlas. Those geometric
existence obligations in the host task remain to be proved.
