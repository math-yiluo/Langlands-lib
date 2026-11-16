# Transporting prescribed characters through completed residue fields

This internal unit combines the actual canonical completed residue maps with
their uniqueness and finite-extension properties. Its ground field `K`, source
and target normed commutative algebras `A` and `B`, and target normed field `L`
have independent universes. `K` is ultrametric. Neither nontrivial norms nor
completeness of `K` are assumed.

## Surjective residue comparison

`completedResidueEquivOfSurjective K f y hs` packages the canonical isometric
map `H(comap f y) → H(y)` as a bounded `K`-algebra equivalence, assuming that
this specific map is surjective. Its forward map is precisely
`completedResidueComap K f y`. Injectivity follows from isometry. The inverse
preserves norms by applying the forward norm identity to an inverse image,
so both directions have bound one.

`character_eq_of_surjective_completedResidueComap` states that two characters
`B →ₐ[K] L` agree when both realize the point norm `y` and agree on the image
of `f`. Here `L` is complete and has a `K`-algebra structure, with no
algebraic-closedness or ultrametric hypothesis. Each character extends to
`H(y)` by `completedResidueLift`. Their composites with the canonical residue
comap agree on `A`, and hence agree on `H(comap f y)` by the existing
completed-residue extensionality theorem. Surjectivity makes the two lifts
equal on `H(y)`. Evaluating on the canonical image of `B` proves the claim.

`existsUnique_character_lift_of_surjective_completedResidueComap` starts with
a prescribed character `g : A →ₐ[K] L` realizing the norm of `comap f y`.
It extends `g` to `H(comap f y)`, composes with the inverse comparison, and
restricts to `B`. The inverse comparison and completed-residue lift are
isometric, so the new character has norm `y`; the evaluation identity for
the comparison proves its restriction is exactly `g`. The preceding
uniqueness theorem proves uniqueness among bounded characters satisfying
both conditions.

These results retain surjectivity as an explicit premise. They do not prove
it for domain inclusions.

## Finite-map lifting

`exists_character_lift_of_finite` assumes that the underlying ring map of
`f` is finite and that `L` is also ultrametric and algebraically closed. It
returns a bounded character of `B` with norm `y` whose restriction is the
prescribed `g`. Finiteness of the actual canonical completed residue extension
gives algebraicity; the existing algebraic character-lifting theorem then
applies. There is no uniqueness claim for this finite-map case.

## Provenance

All assertions are internal deductions from the Library's completed residue
quotient, fraction field, completion, canonical lifts, and norm identities,
together with the finite completed-residue theorem and extensionality lemmas.
No further assertion from the literature is used. The unit supplies transport
interfaces for constructing compatible chart characters, and does not itself
prove the geometric-point axioms of the analytic étale site.
