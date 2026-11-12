# Representative independence of actual canonical standard scalars

Author: Worker 200 (previous FormalGeyser instance).

## Target and provenance

`Langlands.Plancherel.conditionalStandardInductionScalarRepresentative` proves
the exact proposition
`Langlands.Plancherel.ConditionalStandardInductionScalarRepresentativeStatement`
in the independent universes `u,uG,uV,uW`. This is an internal derived result
about the actual standard-integral families and the canonical scalar already
defined by `StandardInductionCanonicalScalar`. It makes no additional claim
to translate an original numbered literature theorem.

## Implemented proof

The proof introduces every datum and premise of the target unchanged. The
two representations are canonical complex `SmoothRep` objects of the same
literal Levi subgroup, connected by the given equivariant linear equivalence.
All subgroups, compact-picture data, characters, measures and normalizations
are fixed on the two sides.

For each direction,
`standardIntertwiningFullDomainRegion_equiv` identifies the two full domains.
This imported theorem applies `domain_eq_top_iff_equiv` to the equivalence
between the actual twists at the same unramified parameter. Thus it transports
both scalar integrability and representability in the original carrier,
at every source vector and group element. The A convergence subsets therefore
also lie in B's corresponding full domains. The proof does not intersect
independently chosen convergence loci.

For both directions, the original operator comparison square is supplied by
`standardInductionIntertwinerFamily_representative_natural`. This theorem is
proved using `fullSourceIntertwiner_natural` for the actual integral, with
the twisted inducing equivalence on both source and target. No comparison
square is an extra premise.

The proof applies
`continuedInductionCompositeRationalScalar_representative_independent` to the
four actual original families and four independently supplied continuation
data. That theorem derives compact naturality from the original squares,
derives generic scalarity from A's actual induced irreducibility, and proves
equality of the rational fractions. It allows independent continuation
denominators and independent normalized coefficients. A's nonempty open
irreducibility locus is retained; no openness of B's locus is needed.

The two normalized coefficients in this application are exactly
`compactInductionScalarExtraction` at the points chosen from A's and B's own
nonempty irreducibility loci, with their own irreducibility proofs. Their
subtype properties supply normalization. These are definitionally the
coefficients in the two canonical scalar definitions. The generic comparison
uses transported A witnesses to show nonemptiness of B's full domains, whereas
the target retains B's independently chosen witnesses. These are proofs of
the same propositions, so proof irrelevance identifies the resulting
expressions. No equality or intersection of the selected loci is assumed.

## Scope

The local field has arbitrary characteristic, and the field, ambient group
and two inducing-carrier universes are independent. The target retains every
subgroup, topology, measure, modulus, convergence, rational-continuation and
actual induced-irreducibility premise. Initial convergence, existence of
whole-operator continuation, generic irreducibility and realization of the
displayed structural data remain application obligations. Representation
and analysis premises do not become permitted external structural inputs
for completing the standing Plancherel program.

The conclusion compares canonical rational scalars for equivalent inducing
representatives with the fixed data of the target. It allows zero operators
and zero scalar. It establishes no nonvanishing, positivity, parabolic-pair,
compact-model or measure independence, opposite relation, source-normalized
`j` or `mu`, or Plancherel conclusion.
