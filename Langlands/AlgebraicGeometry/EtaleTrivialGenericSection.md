# Generic sections from an arbitrary étale constant trivialization

This internal derived module composes the connected cover refinement and its
trivialization restriction with the connected-cover generic-section extension
theorem. All schemes and the index type lie in a common arbitrary universe.

Let `R` be a commutative domain DVR, `K` its specified fraction field with its
original algebra structure, and `C` a relative scheme over `Spec R` with
separated structure morphism. Suppose a supplied étale surjection
`q : U ⟶ Spec R` identifies the pullback of `C` with the coproduct of `I`
copies of `U`, as an actual isomorphism over `U`. The cover may be disconnected
and the index type may be infinite. Every specified `K`-point `p` of `C`
extends to a unique integral section of `C`.

The proof uses `connectedEtaleRefinementOpen` to replace the given cover by a
connected open subscheme still étale and surjective over the base. The
isomorphism `connectedEtaleRefinementTrivialization` retains the supplied
constant trivialization and its exact index type on this refinement. Applying
`existsUnique_section_of_connected_etale_trivialization` then supplies existence
and uniqueness over the original DVR. `sectionOfEtaleTrivialization` chooses
that section; its generic restriction and uniqueness laws are the two
components of this unique-existence proof.

The restriction uses the original `Spec.algebraMap R K` and equality in the
slice over `Spec R`. No henselian, completeness, residue-field, finite-index,
or quasi-compact-cover assumption is made. A constant trivialization remains
an explicit hypothesis; this module does not construct the outer quotient of
reductive groups or prove its geometric properties.
