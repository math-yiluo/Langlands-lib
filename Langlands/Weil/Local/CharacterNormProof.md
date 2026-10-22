# Actual-local character normalization and norm hypotheses

Author: Worker 85.

This module proves four existing targets from
`Langlands.Weil.Local.RepresentationStatements`. Each theorem takes
`{p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)`. The character normalization
theorem also retains the independent representation-carrier universe `v`.

| Theorem in `Langlands.Weil.Local` | Existing target |
| --- | --- |
| `localWeilCharacterNormalizationFor.{u,v}` | `LocalWeilCharacterNormalizationFor.{u,v} F` |
| `localUnramifiedCharacterClassificationFor.{u}` | `LocalUnramifiedCharacterClassificationFor F` |
| `localNormFaithfulnessFor.{u}` | `LocalNormFaithfulnessFor F` |
| `localFrobeniusHypothesesFor.{u}` | `LocalFrobeniusHypothesesFor F` |

The statement module and every pair it imports are unchanged. These results
are the fifth, sixth, eighth and ninth components of
`LocalWeilRepresentationStatements`; the remaining components are outside
this module's scope.

## Unramified characters

Let `Phi = localGeometricFrobenius F`. Its degree is `+1`, proved in
`Assembly` using `localDegree_surjective`. For each `g`, the element
`g / Phi ^ localDegreeInt F g` has degree zero and belongs to actual inertia.
If an algebraic character `χ` is trivial on inertia, applying `χ` to this
element gives
`χ g = χ Phi ^ localDegreeInt F g`. Thus `χ` equals the constructed
`localUnramifiedCharacter F (χ Phi)`.

Continuity follows from that equality and the continuity of the constructed
degree character. The unique parameter is `χ Phi`, including the required
evaluation equality in the conclusion. Conversely,
`localUnramifiedCharacter_on_inertia` shows that every such character is
trivial on inertia. No classification witness or continuity assumption is
supplied as input.

## Determinant and rank-one normalization

Specialize the published `Langlands.Weil.representationCharacterNormalization`
to `localWeilGroup F` and the actual carrier and action of `A`. The definition
of `A.IsContinuous` is exactly the continuity assumption with the endomorphism
module topology required there.

Bundle the algebraic determinant character with its proved continuity to
obtain a continuous homomorphism. Its complex values equal the determinant;
pointwise equality of those values proves uniqueness, including in rank zero.

In rank one, the generic result supplies a continuous algebraic character
and an actual representation equivalence. The published
`FiniteRepresentation.determinantCharacter_eq` transports determinants
across this equivalence. `LinearMap.det_ring` evaluates the determinant of
the scalar-character representation, proving that the character equals the
original determinant pointwise. Bundling its continuity preserves the
equivalence. The determinant equality again proves uniqueness among
continuous homomorphisms satisfying the complete conclusion. Uniqueness of
the representation equivalence itself is not claimed.

## Norm faithfulness and Frobenius hypotheses

Write `q = F.canonicalTopologicalData.residueCardinality`. The published
`residueCardinality_gt_one` gives `q > 1`. The private helper
`cardinality_zpow_eq_one_iff` takes complex norms and uses the injectivity of
integer powers of the positive real number `q`: `(q : ℂ)^n = 1` holds
exactly when `n = 0`.

The formula `localNormCharacter_apply` is `q^(-localDegreeInt F g)`.
The helper therefore identifies the norm kernel with the degree kernel,
which is `localInertia F`. If both the degree and an integer exponent `n`
are nonzero, equality of the `n`th norm power with one would give
`(-localDegreeInt F g) * n = 0`, a contradiction.

The exact `Frobenius.NormCompatible` conclusion is the conjunction of
`q > 1` and the same norm formula. The remaining `CompactSpace` conclusion
follows from `localInertia_isCompact` via the compact-space instance on a
compact subtype. The degree kernel and actual inertia are definitionally
equal, so no separate identification or assumed compactness is required.

## Provenance

This is an internal specialization and derivation from published project
mathematics. The inherited source map is documented in
[`RepresentationStatements.md`](RepresentationStatements.md), and the
generic normalization proof is documented in
[`CharacterNormalizationProof.md`](../Representation/CharacterNormalizationProof.md).
The local constructions and assembly facts are documented in
[`Assembly.md`](Assembly.md) and [`AssemblyProof.md`](AssemblyProof.md).
The residue-cardinality inequality is proved in
[`Normalization/Proof.md`](../../LocalField/Normalization/Proof.md).

The implemented proof uses the existing geometric-degree convention and
ordinary complex topology throughout. It adds no arithmetic hypotheses,
classification data, reciprocity map, or local Langlands correspondence.
All imported results are reused by Lean name.
