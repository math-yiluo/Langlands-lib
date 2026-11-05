# Local polynomial sources for actual Artinian tests

This internal algebraic construction supplies an ambient local polynomial
source for the Picard deformation argument. It uses the actual augmented
Artinian tests of `ArtinianTests` and the actual quotient tower of
`LocalAdicArtinianTests`. Its provenance is the polynomial evaluation and
localization universal properties, together with the noetherian polynomial
and localization instances in Mathlib. It uses no external representability
assertion.

Fix a universe `u`, a commutative ring `k : Type u`, a field `K : Type u`
with its specified `k`-algebra structure, a variable type `σ : Type u`, and
an algebra homomorphism
`ε : MvPolynomial σ k →ₐ[k] K`. Initially neither finiteness of `σ` nor
surjectivity of `ε` is required. The actual tests `A` have a specified
surjective augmentation `A.augmentation : A.algebra →ₐ[k] K`.
They need no `K`-algebra structure or section of that augmentation.

`residueIdeal ε` is the prime ideal `ker ε`.
`ring ε` is literally `Localization.AtPrime (residueIdeal ε)`, and
`polynomialMap ε` is the original algebra map into this localization.
Elements of the prime complement have nonzero image in the field `K`,
so `augmentation ε` extends `ε` by localization. The identity
`augmentation_polynomialMap` is its exact triangle.
`augmentation_surjective` proves that a surjective `ε` gives a
surjective augmentation of this same local source.

For an actual test `A`, `Maps ε A` is the subtype of all actual
`k`-algebra maps from `ring ε` to `A.algebra` whose composite with the
specified augmentation equals `augmentation ε`. `Coordinates ε A`
is the subtype of functions `a : σ → A.algebra` such that
`A.augmentation (a i) = ε (MvPolynomial.X i)` for every variable `i`.
`coordinates` reads these variable values from a source map.

To construct `extend`, first evaluate polynomials at the given coordinates.
Polynomial algebra-map extensionality proves that this evaluation has the
correct residue composite. The surjective augmentation of the local test
is a local homomorphism, so it reflects units. A denominator outside
`ker ε` has nonzero, hence invertible, image in `K`, and therefore its
evaluation is invertible in `A.algebra`. Localization consequently
extends the evaluation. Localization algebra-map extensionality proves
its augmentation triangle.

`extend_polynomialMap` identifies its polynomial composite exactly.
Evaluation on variables gives `coordinates_extend`; localization and
polynomial extensionality give `extend_coordinates`. The resulting
`coordinateEquiv` is an equivalence between all the source maps just
described and all their allowed coordinate functions.
`maps_nonempty` chooses preimages of the prescribed variable residues
under `A.augmentation`, then applies `extend`.

`postcomp ε q` composes source maps with the actual algebra map of
a test arrow `q : A ⟶ B`. For every surjective such arrow,
`postcomp_surjective` proves that every augmentation-compatible source
map to `B` lifts to one to `A`. Choose preimages under `q` of the
variable values of the given map. The augmentation triangle of `q`
proves that these lifted values have the original residues.
Applying `extend` gives the lift, and injectivity of `coordinateEquiv`
proves its exact postcomposition equation. This argument includes
nonsplit augmented tests and imposes no condition on the kernel of `q`.

Now assume `σ` finite, `k` noetherian, and `ε` surjective.
The finite-variable polynomial ring and its localization are
noetherian. Thus `test ε hε n` is the actual test
`ring ε / m^(n+1)` supplied by `LocalAdicArtinianTests`, where `m`
is the maximal ideal of the local source. Numbering starts at its
residue quotient. `projection` and `transition` are the original
quotient map and the original later-to-earlier quotient arrow.
`ofStage` turns a stage arrow into its actual source map by
precomposition with `projection`.

`exists_stage_map` proves that every actual test receives an actual
arrow from some stage. It chooses a source map using `maps_nonempty`
and applies the factorization theorem of `LocalAdicArtinianTests`.
For a surjective test arrow `q : A ⟶ B` and an arrow
`β : test ε hε n ⟶ B`, `exists_stage_lift` gives
`m ≥ n` and an arrow `α : test ε hε m ⟶ A` such that
`α ≫ q = transition ε hε hnm ≫ β`.
The proof first lifts the source map of `β` by
`postcomp_surjective`. Nilpotence of the maximal ideal of `A`
provides a power of the source maximal ideal killed by this lift.
Take the maximum of that bound and `n`, factor through that quotient,
and prove the square by precomposing with the quotient map.
The factorization and transition projection identities give the
two required composites. The theorem allows passage to a later
stage; it does not assert a lift at the original stage.

Finally, `finitePresentation k K` chooses a finite polynomial
presentation whenever `Algebra.FiniteType k K` holds. It uses
Mathlib's `Algebra.FiniteType.iff_quotient_mvPolynomial''` and
renames the variables by the equivalence
`ULift.{u} (Fin d) ≃ Fin d`. This puts the variable type in
the original universe `u` while preserving surjectivity.
With `k` still noetherian, `finiteTypeTest k K` is the actual
tower of this one chosen source. `finiteType_exists_stage_map`
and `finiteType_exists_stage_lift` specialize the preceding
existence and lifting results to it. These statements preserve
the original `k`-structure, including when `K/k` is inseparable;
they do not choose a coefficient field inside any test.

The construction supplies a local polynomial ring and actual
Artinian quotients with the stated lifting properties. It constructs
no completion, no Picard family, no formally versal family or hull,
and no algebraization or smooth scheme atlas. The existence and
geometric comparison arguments for those objects remain separate
obligations.
