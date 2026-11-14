# Assembling the paired derivative root datum

This is an internal construction supporting the root-datum clause of
Kaletha–Prasad Axiom 4.1.22(6). It isolates the algebraic assembly after the
geometric comparisons in Theorem 8.4.10(2) and Proposition 9.4.23. It does not
prove either geometric comparison or the unramified facet statement.

The definition `apartmentDerivativeRootDatumOfRootComparison` constructs a
root datum indexed by the actual quotient roots, together with proofs of its
quotient interpretation and paired graph equality. The theorem
`hasApartmentDerivativeRootDatum_of_rootComparison` supplies the finite index
witness and the resulting existential predicate. They apply to a
supplied building, relative-component model, quotient and integral split torus,
including a torus with conjugated generic inclusion. It assumes:

- The supplied quotient is connected reductive, and the composite special-fibre
  torus inclusion into the quotient is a closed immersion.
- Its actual relative roots are exactly those characters whose inverse
  specialization is the derivative of an affine root vanishing everywhere on
  the supplied apartment subset.
- Each such derivative root has an actual rational quotient point normalizing
  the special torus. The associated torus automorphism acts on characters by
  the reflection formula using that root and the specialization of its supplied
  generic coroot.

No facet hypothesis is needed for this conditional construction. The comparison
inputs determine which subset can satisfy the conclusion.

The proof sends each quotient root through inverse character specialization to
its generic derivative root. It defines the quotient coroot to be the
specialization of that generic root's coroot and chooses the supplied actual
normalizer representative. The pairing of a root and its coroot is two by
`IntegralTorusData.latticePairing_specialization`. The resulting data therefore
form `RelativeRootReflectionData` for the actual quotient inclusion.

The special torus is split by base change. The actual quotient roots are finite
by the finite Lie-weight support theorem, and the full character-lattice Weyl
image is finite by `splitTorusWeylImageFinite`. The proof applies
`RelativeRootReflectionData.rootDatumOfFiniteWeylImage` and its
`isRootDatumOf_rootDatumOfFiniteWeylImage` theorem. Finally, it proves equality
of the full root-coroot graph in both directions using the mutually inverse
character specialization maps. It identifies the specified coroot of every
root, rather than only the two unpaired sets of roots and coroots.

The provenance of this internal result is composition of the published
finite-Weyl-image assembly with the published pairing compatibility for the same
integral torus. The source root criterion and specialization of normalizers
remain explicit hypotheses.
