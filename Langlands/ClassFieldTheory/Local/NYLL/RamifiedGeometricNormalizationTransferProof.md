# Geometric residue normalization at ramified finite abelian levels

Worker 95 proves
`Langlands.LocalClassField.NYLL.RamifiedGeometricNormalizationTransferStatement`
by `ramifiedGeometricNormalizationTransfer` in the same namespace, in arbitrary
independent universes `u` and `v`. This is a derived proof of the published
target in `Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement`.
It imports the published theorems `finiteInertiaFieldUnramified`,
`finiteInertiaResidueMapBijective`, `finiteInertiaResidueRestriction` and
`suppliedInverseResiduePower`.

For the prime `p`, base `F`, extension `E` and supplied realizations `TF`, `TU`
and `TE` in the target, let `U = finiteInertiaPadicField F E TF` and
`q = TF.residueCardinality`. The proof installs the target's local instance
`finiteInertiaField_isAbelianGalois F E TF`. It applies the given family's
unramified normalization to this actual `U`, using
`finiteInertiaFieldUnramified` for its relative ramification index one.
Evaluation of the given equality of homomorphisms at `a` identifies
`Artin U TU a` with the restriction of `Artin E TE a`.

The equivalence `suppliedInverseResiduePower` converts this normalization
into the identity that the inverse residue action of that restricted
automorphism is `y ↦ y ^ q` on `TU.ResidueField`. The proof applies
`finiteInertiaResidueRestriction` to `(Artin E TE a)⁻¹`. Since restriction
and the residue actions preserve inverses, its symmetric equality transports
the inverse action through the specific inclusion
`j = finiteInertiaResidueMap F E TF TU TE`. Applying the power identity and
`map_pow` gives the inverse-action formula on every `j y`.
The surjectivity component of `finiteInertiaResidueMapBijective` covers every
element of `TE.ResidueField`. Finally, `suppliedInverseResiduePower` for `E`
converts that identity into the exact discrete-valuation congruence on every
integral `x : E.Carrier`.

The derivation uses exactly the supplied realizations and actual maps of the
published statement. Its provenance is the derived route documented in the
paired `RamifiedResidueStatement.md`: transfer from the inertia fixed field,
using the four independently published bridge theorems above. This proof
introduces no new assertion from the external literature. The result retains
one and the same `Artin` family throughout, and the unramifiedness premise is
used only for `U/F`. It adds no premise on `E/F`. The target's Lean/Markdown
pair and its import closure are unchanged. Specialization to the named NYLL
Artin family remains a separate result.
