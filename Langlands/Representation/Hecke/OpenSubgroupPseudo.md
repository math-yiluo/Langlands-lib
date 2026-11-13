# Pseudo-forgetting for an open subgroup

This internal helper proves the pseudo-forgetful comparison in Renard III.2.6,
final Remark (printed p.77 / PDF p.83), using the nondegenerate-module argument
recalled at the end of I.2.3 (printed p.18 / PDF p.24). The registered source is
Renard's 9 July 2026 edition, `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The construction `Langlands.Hecke.Homomorphism.OpenSubgroup.pseudoFIsoF` compares
the published functors `pseudoF` and `F` for an open subgroup, arbitrary Haar
measures and an independent module-carrier universe. It uses the normalized
inclusion and its right action identity from `OpenSubgroupHeckeBasics`.

The comparison sends a regular tensor `t` to the orbit map
`b ↦ b • contraction(t)`. The general balancing identity for the two specified
Hecke actions proves module linearity and membership in the nondegenerate Hom
part. Injectivity follows from contraction injectivity and nondegeneracy.
For a Hom element `ψ` fixed by a subgroup idempotent `e`, the right action identity
gives `ψ(b) = ψ(b * inclusion(e)) = b • ψ(inclusion(e))`. A local unit for this last
value supplies a tensor preimage. Naturality follows from naturality of regular
tensor contraction, giving the natural isomorphism.

The proof adapts the Library's `NormalQuotientPseudo` regular tensor/Hom argument;
the new input is the open-subgroup right action identity. No restriction or
normalization of the two supplied Haar measures is assumed.
