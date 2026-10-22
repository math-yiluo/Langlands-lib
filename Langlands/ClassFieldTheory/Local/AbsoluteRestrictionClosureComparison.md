# Absolute restriction along explicit closure embeddings

Author: Worker 160.

This module constructs explicit-embedding wrappers for the published actual
closure-unit coefficient inclusion and continuous absolute cohomology restriction.
It proves their composition formula for a source-closure automorphism and the
resulting factorization comparing any two compatible closure embeddings.

## Scope and constructions

Let K and L be arbitrary fields in one arbitrary common universe, with a fixed
K-algebra structure on L. A compatible embedding is a K-algebra homomorphism
ι : AlgebraicClosure K → AlgebraicClosure L; the K-action on the target comes
through L. No finite-dimensionality, Galois, characteristic-zero, or local-field
hypothesis is imposed. The common universe matches the published absolute
cohomology API and its lifted integer scalars.

`absoluteRestrictionAlongClosureCoefficients ι` installs the algebra structure
`ι.toAlgebra` and uses `absoluteRestrictionCoefficients K L`. Its source is the
restriction of `absoluteUnits K` along `restrictionAlongClosure ι`, and its target
is `absoluteUnits L`. These are the actual discrete additive closure-unit
representations. The evaluation lemma
`absoluteRestrictionAlongClosureCoefficients_apply` states that the underlying
field element of the image of a unit x is ι(x).

`absoluteRestrictionAlongClosure ι n` is `ContinuousCohomology.map` for that
continuous group homomorphism and that coefficient morphism. Thus it is a
morphism from `absoluteCohomology K n` to `absoluteCohomology L n`, for every
natural-number degree n, using the existing continuous-cohomology objects.

## Implemented identities

Write rι for `restrictionAlongClosure ι` and Rι for the newly constructed
cohomology map. For an element c of the absolute Galois group of K,
`restrictionAlongClosure_comp_automorphism` proves

    r(ι ∘ c) = rc ∘ rι.

The proof applies the injective embedding ι ∘ c to each automorphism value and
uses the published normal-restriction commuting identities. Explicit
`AlgEquiv.toRingEquiv` expressions keep the absolute Galois group wrapper and
its field-automorphism coercions aligned.

`absoluteRestrictionAlongClosure_comp_automorphism` proves

    R(ι ∘ c) = Rc ≫ Rι.

Here the category notation means first apply Rc and then Rι. The proof uses
`ContinuousCohomology.map_comp`, the preceding group-map equality, and
extensional equality of the two coefficient inclusions on units. A private
congruence helper first substitutes equality of the group homomorphisms, then
identifies the coefficient morphisms pointwise. It is stated for abstract
topological representations to avoid expensive elaboration through the
concrete algebraic-closure coefficients.

For two embeddings ι and κ, the published `closureChange ι κ` is the source
closure automorphism c characterized by ι(c x) = κ(x).
`closureChange_comp_embedding` identifies ι ∘ c with κ by that characterization.
Finally, `absoluteRestrictionAlongClosure_change` proves, in every degree,

    Rκ = R(closureChange ι κ) ≫ Rι.

## Provenance and limits

This is an internal construction from the published
`Langlands.ClassFieldTheory.Local.Cohomology` and
`Langlands.Galois.ClosureRestriction` interfaces, together with the pinned
Mathlib continuous-cohomology functoriality theorem. The formulas follow from
those definitions and the implemented proofs above; no new source theorem or
external mathematical hypothesis is introduced.

The factorization is one prerequisite for the published
`AbsoluteRestrictionClosureIndependence` statement. The present module does
not prove that the source-automorphism cohomology map is the identity, does not
prove closure independence, and does not construct a local invariant or prove
its degree law. Those remain separate proof obligations.
