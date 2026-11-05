# Surjective complete local polynomial presentations of actual Artinian tests

This internal construction supplies an actual equation presentation of an
augmented local Artinian test. It is a prerequisite for constructing successive
quotients supporting a formal Picard family. It does not construct that family
or assert a hull or versality theorem.

Let `k` be a commutative ring and `K` a field with its given `k`-algebra
structure. An `ArtinianTest k K` is an actual local Artinian `k`-algebra `A`
with a specified surjective augmentation `A → K`. No section of the
augmentation or `K`-algebra structure on `A` is required.

If `K` is finite as a `k`-module, `moduleFinite` proves that `A` is finite
as a `k`-module. The augmentation kernel is a finitely generated nilpotent
ideal, since `A` is Artinian and therefore Noetherian. Mathlib's
`Module.finite_of_surjective_of_ker_le_nilradical` then applies directly to
the actual augmentation. Over a Jacobson scalar ring, a field that is a
finite type algebra is finite as a module by Mathlib's Zariski lemma;
`moduleFinite_of_finiteType` records this specialization. Fields are included.

Choose a finite polynomial algebra surjecting onto the entire algebra `A`,
and compose that presentation with its specified augmentation to obtain a
surjective polynomial residue map. The variable type is an `ULift` of a
finite ordinal, so it stays in the same arbitrary universe `u` as `A`.
The existing `LocalPolynomialArtinianSource.extend` extends the chosen
generator values to the localization at the residue kernel. This is still
surjective: its image contains the image of the original surjective
polynomial presentation.

Assume further that `k` is Noetherian. The localization is Noetherian, and
its actual maximal-ideal completion is a complete Noetherian local ring.
The established `CompletedLocalPolynomialSource.localMapEquiv` extends
the local cover to that actual completion. The lemmas
`cover_sourceMap` and `cover_polynomialMap` prove that the extension retains
the original generator values, and `cover_surjective` proves that it still
surjects onto the whole test. `augmentation_cover` retains the exact
original residue equation.

The actual kernel `equations` is finitely generated, lies in the complete
source's maximal ideal, and contains a positive power of that ideal.
`quotientEquiv` is the ordinary quotient-by-kernel algebra equivalence
with the unchanged actual test algebra. Its reduction is exactly the
specified residue augmentation.

The provenance is internal: finite generation through a nilpotent kernel,
finite polynomial presentations, localization, the previously established
Artinian mapping property of completion, and the ordinary algebraic first
isomorphism theorem. Neither a coefficient field nor separability of `K`
over the scalar ring enters the proof. The source and its equations depend
on choices of a polynomial presentation; no uniqueness of that choice is
claimed.
