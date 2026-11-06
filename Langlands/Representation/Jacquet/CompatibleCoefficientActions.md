# Compatible coefficient actions on actual compact and Jacquet fixed vectors

Worker 1755, with interface and reuse guidance from Worker 1751. Internal
constructions for the coefficient-linear application of Renard 2026 VI.9.2,
printed p.199 / PDF p.205. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These constructions make explicit the commuting coefficient actions in that
application; they are derived implementation content, rather than a verbatim
statement from the book.

Let `R` be a commutative ring, let `V` have its given additive group and both
complex and `R`-module structures, and let `ρ` be an actual complex group
representation. `HasCompatibleCoefficients R ρ` is the intrinsic law
`ρ g (r • v) = r • ρ g v` for every `r`, `g` and `v`.
It asserts no existence, finiteness or stability property.

`Langlands.coefficientFixedVectors` is the actual complex fixed-vector set
as an `R`-submodule of `V`. Its carrier is unchanged, so the inherited module
instance `coefficientFixedVectorsModule` equips that same complex fixed-vector
carrier with `R`-scalars. Its value law is `(r • x).val = r • x.val`.
These constructions need no commutation hypothesis between the two scalar
actions on `V`.

For the quotient constructions, the additional `SMulCommClass ℂ R V`
requires the given complex and coefficient actions to commute.
`Jacquet.coefficient_smul_mem_relations` proves by complex span induction
that the actual complex Jacquet relation set is stable under coefficient
scalars. At a generator, this follows from group/coefficient compatibility;
the complex scalar step uses the commuting scalar actions.
`coefficientRelations` is this literal relation set regarded as an
`R`-submodule. Its quotient and the existing complex coinvariants quotient
have the same underlying additive relation, so
`coefficientCoinvariantsModule` gives an `R`-module structure on the actual
complex quotient. The proved value law is
`mk ρ N (r • v) = r • mk ρ N v`.

By taking representatives, `action_hasCompatibleCoefficients` proves
compatibility of the unnormalized action of every normalizing subgroup
with these quotient scalars. Hence its actual complex fixed-vector space
also acquires the inherited `R`-action. All these constructions have
independent coefficient, group and representation-carrier universes.

`coefficientIntertwiner R ρ r` is the actual complex intertwiner
`v ↦ r • v`. Its restriction to fixed vectors is precisely coefficient
multiplication. Applying the published compression naturality law to this
intertwiner proves `compressedAction_coefficient_smul`.
The representative scalar law proves `fixedJacquetMap_coefficient_smul`.
Compatibility of the unnormalized action proves
`fixedJacquetCentralEquiv_coefficient_smul`.

The final corollary
`fixedJacquetMap_surjective_and_eventuallyStable_of_compatible_coefficients`
applies the `CompressionCoefficientLocalization` adapter with
these three proved laws. It assumes smoothness, compactness of `K`,
the actual Iwahori contraction and normalizer conditions, Levi centrality,
Noetherianity of `R`, and finite generation over `R` of both actual fixed
spaces. It concludes surjectivity of the actual fixed Jacquet quotient and
`EventuallyStable` for the original complex compressed action, including
a positive exponent and both square kernel/range equalities.

Finiteness is assumed only in that last corollary, and it remains an
obligation for applications to universal families. None of the constructions
asserts that compatible coefficient actions or finite coefficient modules
exist for arbitrary smooth representations. No representation-uniform
exponent or unconditional instance of the host theorem is proved here.
