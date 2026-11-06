# Separation by actual finite abelian norm groups

`Langlands.LocalClassField.normSubgroupsSeparatePoints` proves the published
proposition `NormSubgroupsSeparatePoints` for every prime and arbitrary carrier
universe. Each nonidentity element of the actual field multiplicative group is
excluded by the actual determinant-norm subgroup of a finite abelian
intermediate extension in its algebraic closure. The theorem adds no hypotheses.

The preparatory theorem
`normSubgroupsSeparatePoints_of_universalNorm_le_finiteIndex` assumes that the
actual universal norm subgroup is contained in every finite-index subgroup.
Apply the proved open finite-index separation
to the canonical topology and a nonidentity field unit. The resulting subgroup
excludes that unit, so the containment assumption excludes it from the
universal norm subgroup. Unfolding universal-norm membership produces an
actual finite abelian intermediate field whose determinant-norm image excludes
the unit. The existential witness, finite dimensionality, and abelian Galois
condition are precisely those required by the published separation statement.

The second preparatory theorem supplies the containment premise using
`universalNorm_le_finiteIndex_of_lifting` from `UniversalNormDivisibility`.
Its assumptions are the exact global
`UniversalNormLifting` input and downward directedness and closedness of the
actual finite abelian norm family. Closedness is needed only for the canonical
topology used in the topological separation argument.

The final theorem discharges all three assumptions using `universalNormLifting`,
`finiteAbelianNormFamily_directed`, and `isClosed_finiteAbelianNormFamily` from
`NormExistenceUniversalLift`, specializing closedness to the canonical topology.
The arbitrary field universe is unchanged throughout. Full norm-subgroup
existence, uniqueness, and a correspondence are unnecessary for this assembly.

The provenance is internal derivation from the actual topological separation
proof, universal-norm divisibility, and universal-norm lifting. The divisibility
result combines Kummer norm symmetry and the local invariant with compact power
fibers. Lifting uses maximal abelian norm reduction, finite normal closures,
norm transitivity, and compact norm fibers. Directedness uses actual composita,
and closedness uses the compact image of integral units and the norm-order law.
These dependencies supply their arithmetic and topological conclusions
unconditionally; the two preparatory conditional lemmas do not add premises to
the final theorem.
