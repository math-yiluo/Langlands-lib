# Actual adelic additive self-duality and the diagonal annihilator

The theorem `Langlands.Global.adelicAdditiveDuality_proof` proves the unchanged
published proposition `Langlands.Global.AdelicAdditiveDualityStatement.{u}`.
It applies to every number field in arbitrary universe `u` and every existing
continuous nontrivial unitary additive character of its actual adele ring that
is trivial on its diagonal field. Both conclusions use the original completion
and restricted-product objects and topologies. The group homeomorphism maps
`a` to the continuous character `x ↦ ψ(a*x)` in the full compact-open
Pontryagin dual. The other conclusion says exactly that a parameter killing
all diagonal field elements belongs to the diagonal field.

The source target is Weil, *Basic Number Theory*, second edition (1973),
Chapter IV, §2, Theorem 3, in the specialization already documented in the
published statement pair. The implemented proof takes a different route. Its
compactness, finite-cover and compact-character arguments were developed
internally from Worker 1843's generic plan, with the actual one-place
approximation constructed by Worker 1786. It assumes neither global nor local
additive self-duality.

## Actual arithmetic and nondegeneracy

`Langlands.Global.exists_compact_sub_diagonal_mem` supplies a
compact set `C` with a representative of every additive field coset. It
combines integral finite-adele representatives with the compact archimedean
fundamental set. `AdelicLocalApproximation.exists_local_factor` starts with a
nonzero actual adele and chooses a place where its component is nonzero. The
one-place idempotent `e` at that place equals `a*z` for an actual adele `z`.
Compact representatives and noncompactness of that completion imply that
nonzero diagonal field elements times `1-e` enter every neighborhood of zero.
The finite-cover argument is supplied by `CocompactLocalApproximation`.

`adelicPairing_nondegenerate` instantiates
`CocompactPairingSeparation.nondegenerate` with these actual inputs. For context,
the generic result uses the open circle arc of radius `π/2`. The parameters
whose multiplication characters send `C` into this arc form a neighborhood of
zero by compact-open continuity. A parameter in this neighborhood that kills
the field kills the entire ring: subtract a field representative, then use
that a character with all values in the arc is trivial. If a nonzero adele
annihilated every adele, the one-place approximation would give a small nonzero
field scalar on the complementary factor. This scalar would then annihilate
the ring, contradicting the nontriviality of `ψ` after multiplying by its field
inverse.

## The diagonal annihilator

`adelicPairing_annihilator` instantiates
`CocompactFieldAnnihilator.mem_iff_range` with the same compact representatives
and the established nondegeneracy. In that generic finite-cover proof, an
annihilating parameter is multiplied by every field scalar and reduced to `C`.
Two distinct scalars have representatives in the same sufficiently small
covering cell. Their difference both annihilates the field and is small, hence
annihilates the ring and is zero. Inverting the nonzero difference of the field
scalars places the original parameter in the field image. Conversely, a field
parameter annihilates the field by the given field triviality of `ψ`.

## All continuous characters

The quotient by the field, written with multiplicative group notation, is
definitionally the existing additive adele quotient. `fieldQuotient_compact`
uses the published quotient compactness theorem, and
`fieldQuotient_hausdorff` uses closedness of the principal adeles.

`adelicPairing_restrictionMatching` chooses the discrete topology on the field
locally and applies `CocompactFieldRestriction.exists_parameter`. The full dual
of this discrete field is compact. The multiplication pairing descends from
the compact adelic quotient to this field dual. Evaluation characters separate
points of the field dual; a nonzero field evaluation pulls back nontrivially,
because its inverse would otherwise force `ψ` to be trivial. The
`CompactCharacterRange` theorem proves this descended map is surjective. Its
proof equates translated Haar averaging functionals on the dense linear span
of evaluation characters. A point outside the compact image would give
disjoint compact cosets; Urysohn's lemma produces a continuous function with
averages zero and one on those two cosets, a contradiction. Thus every
continuous adelic character agrees with some multiplication character on the
whole diagonal field.

`CocompactRingCharacters.exists_field_parameter` handles continuous characters
trivial on the field. The annihilator identity says that the characters with
field parameters separate points of the compact adelic quotient.
`CompactQuotientCharacters` descends these characters and uses
`CompactCharacterCompleteness`: Stone–Weierstrass makes their complex span
dense, and Haar integration excludes any additional character by orthogonality.
For a general continuous character, divide by the matching multiplication
character, apply this field-trivial parametrization, and add the two
parameters. This is `CocompactRingCharacters.pairing_surjective`.

## Topology and the exact target

`adelicDuality` combines this surjectivity with nondegeneracy for injectivity.
`RingPontryaginPairing.hom` is continuous for the full compact-open topology by
joint continuity of multiplication and compact-open currying. The actual adele
ring is locally compact and second countable by the imported published
results, hence sigma compact. The topological-group open mapping theorem
therefore makes this continuous surjection open.
`RingPontryaginPairing.equivOfBijective` produces the group homeomorphism. Its
evaluation is definitionally `ψ(a*x)`. The second conjunct is the separately
proved actual diagonal-annihilator identity. Finally,
`adelicAdditiveDuality_proof` introduces all quantified data of the published
proposition and applies `adelicDuality`, with no remaining auxiliary premises.
