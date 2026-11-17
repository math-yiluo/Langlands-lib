# Local exponent descriptions of actual split-torus homomorphisms

For arbitrary schemes `S`, `S′`, a map `q : S′ → S`, and finite coordinate
sets `I`, `J`, `splitTorus.pullHom τ q` is the actual base change of a
homomorphism `τ : G_m^I → G_m^J`, conjugated by the canonical coordinate
base-change isomorphisms. `pullIso` performs the same construction for an
actual isomorphism and has this homomorphism as its forward map.

`homFamily τ` is postcomposition by the given homomorphism, regarded as a
family over the terminal `S`-test. It is multiplicative and natural.
`pointsEquiv_pullHom` identifies the action of the normalized pullback on
points with the original action under the actual pullback adjunction.
`actsBy_iff_pullHom` consequently identifies the published family predicate
`HomFamily.ActsBy` with the monomial formula for `pullHom` on every relative
test over `S′`. The reverse implication uses affine tests and
`famUnits_congr` to retain the explicitly equal structural base maps.

For a supplied linear character map `f : (J → ℤ) →ₗ[ℤ] (I → ℤ)`,
`weightMatrix f` has row `j` equal to `f (Pi.single j 1)`. The lemma
`rectPow_character` proves that its monomial map transports every character
by `f`: expand the linear map in the standard coordinate basis, interchange
the two finite products, and combine integral powers. Thus
`characters_iff_pullHom` equates the entire-character formula with the
matrix family predicate; one direction tests the coordinate characters and
the other uses the finite-product calculation.

`exists_open_character_pullHom` assumes that this same supplied `f` describes
the normalized pullback at the residue field of a specified point of `S`.
It produces an open neighbourhood of that point on which `f` describes the
actual normalized pullback on every relative test scheme and every integral
character, including all central directions. Its proof converts the supplied
residue formula into `ActsAtPoint`, uses the published local constancy of
that predicate to keep this particular matrix on an open neighbourhood,
and applies `actsBy_of_forall_actsAtPoint_on` there. It requires no connectedness,
affineness or reducedness assumption on `S` and no matrix uniqueness argument.

This is an internal construction derived from the published split-torus
point equivalences, pullback adjunction, exponent transport and homomorphism
family rigidity/locality results, with the standard coordinate matrix identity
from Mathlib. It asserts no new original-literature theorem. A residue-field
formula is a premise: this unit does not itself construct a root-datum
comparison, align pinning vectors or prove relative comparison existence.
