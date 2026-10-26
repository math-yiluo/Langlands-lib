# Galois transport of actual cocharacter weight ranks

This module proves
`Langlands.Shimura.CentralSimpleUnitaryData.ComplexCocharacterGaloisWeightRanks`.
The arithmetic datum, compatible CM section, and Harris signature charts are
exactly those of the target. The Galois automorphism is any rational algebra
automorphism of the complex numbers, and the cocharacters are genuine morphisms
of complex group schemes.

For a cocharacter in the direct rational base-change model, write `a(u)` for its
matrix coordinate at `i`. The actual transport formula identifies the coordinate
of the transported cocharacter at `s ∘ i` with the chart comparison applied to
the entrywise image of `a(s⁻¹(u))`. The constructed
`embeddingChartConjugator` identifies this family with
`U * coefficientWeightFamily s a u * U⁻¹`, where `U` is independent of `u`.
Conjugation invariance of the inverse-weight rank removes `U`. The published
semilinear equivalence of inverse-weight submodules then identifies the remaining
rank with that of `a`. These two numerical equalities prove
`finrank_directCocharacterWeightSpace_galois`.

`finrank_complexCocharacterWeightSpace_galois` rewrites both weight submodules
using the canonical comparison with the direct model. The compatibility of
Galois transport with this comparison reduces the equality to the first result.
`finrank_complexCocharacterWeightSpace_galois_kottwitz` specializes to the
first-factor Kottwitz cocharacter and applies the existing identification of
its inverse-weight rank with `realHodgeFunction C i`. Thus the first-factor
and inverse-weight conventions are retained.

`complexCocharacterGaloisWeightRanks` packages the direct-model equality,
the iterated-model equality, and the Kottwitz Hodge-rank equality as the exact
three conjuncts of the target. The proof establishes rank transport; it does
not classify cocharacters or assert descent or a reflex-field stabilizer theorem.
This is an internal derivation from the named constructions and their comparison
identities, with no additional literature claim.

The chart-conjugator construction and rank proof are due to Worker 57, whose
shared Lean draft is reused unchanged. Worker 401 checked the proof and
prepared the submission against the published dependencies. The imported
matrix-innerness proof is due to Worker 277; its published module is a
dependency and is not included in this contribution. The target statement
and all its imported Lean and Markdown files remain unchanged.
