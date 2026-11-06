# Reconstruction from coherent finite Artin families

This internal construction works for any perfect field `K : Type u`, with an
arbitrary supplied topology on `K`. It starts with a supplied
`FiniteArtinFamily K` and `FiniteArtinRestrictionRelation` certificate. It does
not assert arithmetic existence or uniqueness of that family.

`extension_antitone` proves that the actual fixed-field extension attached to
an open subgroup reverses inclusions. `restrictionOfLE_comp` proves that finite
restriction followed by the smaller-field restriction equals direct restriction
from the actual Galois abelianization. The proof descends to representatives
of the closed-commutator quotient and applies Mathlib's restriction-composition
identity for algebraic automorphisms.

`restrictionKernel` is the actual open kernel of restriction to a finite
abelian intermediate extension. It is open because the finite Galois group has
the discrete Krull topology. `extension_restrictionKernel` recovers the same
intermediate extension from that kernel, using Mathlib's infinite Galois
fixed-field correspondence. `quotientEquiv_map` identifies the open-group
quotient transition with actual field restriction.

`quotientFamily` transports each supplied finite Artin component through the
inverse of the actual quotient equivalence in
`AbelianGaloisFiniteQuotients`. Its target is the corresponding finite group in
Mathlib's profinite quotient diagram. Continuity of this transport uses the
discrete topology on the source finite Galois group. The supplied compatibility
proves `quotientFamily_compatible`. Thus `limitHom` is a continuous homomorphism
to Mathlib's actual compatible-coordinate inverse limit; continuity is checked
coordinate by coordinate in the product topology. `reconstruct` composes it
with the inverse of Mathlib's
`ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`.

`reconstruct_quotient` proves the coordinate identity using the inverse law of
that equivalence. `reconstruct_extension` then identifies restriction to each
field attached to an open kernel. Applying this to `restrictionKernel` proves
`finiteFamilyOfHom_reconstruct` for every actual finite abelian extension,
including the original extension object and its actual automorphism group.

`finiteRestriction_separates` uses injectivity of Mathlib's map to the
finite-quotient limit and the quotient equivalences: equality in every actual
finite restriction forces equality in every open normal quotient.
`finiteFamilyOfHom_injective` applies this pointwise to continuous homomorphisms.

`denseRange_of_finite_surjective` proves that a candidate homomorphism with
surjective restrictions to every actual finite abelian extension has dense
range. Given a point of a nonempty open set, translate the set to a neighborhood
of one and choose an open normal subgroup inside it. Surjectivity onto the
Galois group of its fixed field gives an image point in the desired coset, hence
in the open set. This uses the actual profinite topology, rather than inferring
density from an abstract group identification.

Finally, `reconstruct_normResidue` proves the full
`ProfiniteNormResidueRelation` from a supplied `FiniteArtinSystemRelation`:
component recovery gives its exact norm kernels, finite surjectivity and all
restriction identities, and the preceding density argument supplies dense
range. Arithmetic existence, geometric residue normalization and unconditional
uniqueness remain separate obligations of the profinite reciprocity proof task.

The provenance is internal: these are structural derivations from the existing
actual field and Galois constructions, Mathlib's infinite Galois correspondence,
and Mathlib's finite-quotient reconstruction theorem. They introduce no new
literature assertion, arithmetic witness or class-field-theoretic premise into
the unconditional target statement.
