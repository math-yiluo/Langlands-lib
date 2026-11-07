# Raw-character Whittaker functionals on actual automorphic local components

Worker 1582 implements the adapter proposed by Worker 1709 for constructing
local Whittaker genericity from a global functional. This is internal derived
infrastructure using the Library's canonical completion comparison,
`PadicLocalCategory`, and `PadicCharacterIndependence`.

A nontrivial circle-valued additive character `χ` on `FiniteCompletion F v`
which is trivial on `v.adicCompletionIntegers F` is bundled as a continuous
unitary additive character of the canonical p-adic field. The proof uses the
published equality of completed integers and canonical integral elements and
the continuity construction from the open level-zero lattice. Its original
values are preserved exactly.

For any actual local realization `S` of rank `r + 1`,
`S.whittakerFunctionalOfIntegerTrivial` bundles a complex-linear functional on
`S.Space` satisfying the positive first-superdiagonal equivariance condition.
Its underlying linear form remains the supplied form `ℓ`, and its action is
exactly `S.representation`.

`S.isGeneric_of_integerTrivial_character` assumes such a form is nonzero and
that `S` is irreducible and admissible. It applies p-adic character independence
to conclude genericity for every continuous nontrivial unitary additive
character of the canonical p-adic topology. Admissibility is transferred by
the proved `S.isAdmissible_canonical_iff`. The conclusion names precisely
`((S.padicObject hI hA).obj.representation)`, which definitionally retains the
original form-space representation and carrier. No equivalence of carriers
is introduced. The construction includes rank one.

This adapter is conditional on the supplied raw character and nonzero
functional. It does not prove their existence for a cuspidal spectral
presentation; that is the separate global Whittaker existence obligation in
the full local genericity proof.
