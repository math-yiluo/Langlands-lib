# Nonlinkage of segments with square-integrable special heads

Author: Worker 167.

The closing theorem
`Langlands.Classification.squareIntegrableSegmentNonlinkage`
proves exactly
`Langlands.Classification.SquareIntegrableSegmentNonlinkage.{uF,uV} F T`
from [SquareIntegrableSegmentNonlinkageStatement](SquareIntegrableSegmentNonlinkageStatement.md).
It preserves arbitrary independent field and carrier universes, every actual
p-adic field `F`, its supplied topology `T`, and the saturated carriers
`max uF uV` of the segments and heads. The two degrees may differ and the
segments may coincide. Its only hypotheses are the two supplied special-head
relations and their actual analytic square-integrability.

This is an internal derivation from the existing segment definitions, analytic
square-integrability, admissible Schur theorem, real determinant powers,
normalized absolute value, uniformizer, and the proved scalar action in
[SegmentConstituentCentralCharacterProof](SegmentConstituentCentralCharacterProof.md).
The statement's original-source provenance is retained; this proof implements
the direct scalar-action route described there. It uses no classification,
exhaustion, tempered block uniqueness, ordered strong-head existence or quotient
coverage theorem, no positive-form exponent data, and no unitary normalization
of a selected cuspidal presentation. The statement pair and all its imports
are unchanged.

For the support comparison, `Segment.support_subset_of_base_shift`, now imported
from [SegmentSupportContainment](SegmentSupportContainment.md) with its original
name, statement and proof, sends the
`i`th member of a segment starting at position `k` in another segment to its
member `k+i`, using `CuspidalDatum.twist_twist`. The translated length bound
ensures that this index is in range. For bases at natural positions `a,b` in a
common twist string and lengths `m,n` with `2a+m=2b+n`,
`support_nested_of_equal_midpoint` orders `a,b` and obtains one of these
containments. `not_isLinked_of_equal_midpoint` then contradicts the appropriate
noncontainment clause in `IsLinked`. These lemmas require no injectivity or
nonperiodicity of the twist action.

For the analytic step, the private lemma `scalarCharacter_norm_eq_one`
specializes square-integrability at an existing Haar measure on the actual
central quotient, extracting the required unitary central character.
Irreducibility supplies a nonzero vector. Equality of the prescribed scalar
action and the unitary central action on this vector shows that the prescribed
scalar character has norm one on every scalar matrix. This step uses only the
unitary-central-character part of the analytic predicate; it does not assert
existence of an invariant positive Hermitian form. The private lemma
`norm_determinantPowerCharacter_scalar` computes the norm of the actual real
determinant-power character at `z I_r` as `|z|^(r s)`, retaining the rank factor.

For a head whose base is the `a`th twist of a common cuspidal datum of rank `r`,
the private lemma `segmentHead_norm_identity` constructs the actual determinant
twist of a representative `A` of that datum. Its isomorphism class represents
the supplied base. Its scalar character is the product of the scalar character
`omega` of `A` and the scalar restriction of the determinant-power character of
exponent `a`. The scalar constituent formula applies to the irreducible quotient
underlying the supplied head. The preceding norm calculation therefore gives,
for length `m` and every nonzero scalar `z`,

```text
norm(omega(z))^m * |z|^(r*m*(a+(m-1)/2)) = 1.
```

The representative remains in its original carrier universe, and the heads
retain the saturated carrier universe required by the public statement.
Destructing the segment and its base equality handles the dependent rank
without resizing or selecting a centered presentation.

The helper `squareIntegrableSegmentNonlinkage_of_centralCharacter` assembles
these steps from the scalar constituent formula. Assuming linkage supplies a
union segment. Membership of the two given bases in its support gives natural
starting positions `a,b`. An actual representative of the union's base class
exists by the quotient construction; the admissible Schur theorem supplies its
scalar character `omega`. At the actual uniformizer, `|z|` is positive and
strictly less than one. The private lemma `midpoint_eq_of_norm_identities` takes
logarithms of the two norm identities. The positive lengths, nonzero common
rank and nonzero logarithm force `2a+m=2b+n`. The support comparison contradicts
linkage.

Finally, `squareIntegrableSegmentNonlinkage` supplies the helper with the proved
`segmentConstituentCentralCharacter.{uF,max uF uV} F T`. Thus no
scalar-character assumption remains in the closing theorem. This imported
formula was proved independently using the actual block tensor product,
trivial scalar half modulus, normalized-induction covariance, determinant
powers and constituent intertwiners. The resulting proof uses the supplied
special heads themselves and does not identify them with parameters obtained
from an exhaustion theorem.
