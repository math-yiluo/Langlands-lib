# Reduction of Harris's Proposition 4.8 to named inputs

`Langlands.Global.Harris.Proposition48ReductionStatement` states that an
explicit conjunction of fourteen named propositions implies the unchanged
`Langlands.Global.Harris.Proposition48Statement.{uF,0,0,0,uV}`.
Both `uF` and `uV` are arbitrary; the three number-field universes are
zero, as required by the existing Henniart globalization consumers.
This file states the reduction and does not prove it.

The fourteen conjuncts, in their Lean order, are:

1. `Proposition48AuxiliaryRankOneStatement`;
2. `Proposition48AuxiliaryParityNormalizationStatement`;
3. `Proposition48AuxiliaryParityUntwistStatement`;
4. `Proposition48MackeyStepStatement`;
5. `Proposition48PrimeBranchStatement`;
6. `Proposition48SingletonBranchStatement`;
7. `Harris1998Theorem12CuspidalStatement`;
8. `HarrisSupercuspidalLocalComparisonStatement`;
9. `CuspidalSpectralRigidityStatement`;
10. `Proposition48IsobaricInvarianceStatement`;
11. `CyclicRegularInductionStatement`;
12. `CyclicRegularOrbitLiftStatement`;
13. `CyclicStableDescentStatement`;
14. `CyclicWeakInductionSupercuspidalStatement`.

The first six use the arbitrary local-field universe `uF` where
applicable. The last eight use small number fields and the arbitrary
carrier universe `uV`. The compatible-family and transfer premises use
`uV` for both carrier universes. The normalization statement has no
automorphic carrier parameter. Every theorem input is an explicit
conjunct. In particular the foundational implications appearing inside
the branch statements are supplied separately here, and no theorem
assumption is stored in the problem or transport definitions.

The intended proof is strong induction on
`Proposition48Problem.inductionDegree = [L:E]` for the one-place valid
problems. Rank one uses the first input. For larger rank the Mackey-step
input chooses one compatible prime cyclic step and supplies actual raw
children for every representative, with smaller closure degree and
the parent's infinity parity. Normalize each child by the second
input. Its corrected problem has the same fields and hence the same
strictly smaller induction degree. Apply the induction hypothesis to
that corrected problem, then the third input to recover actual raw
and corrected realizations related by the genuine determinant twist.
These data are precisely the existential hypotheses of the prime and
singleton branch statements. The cardinality alternative from the
Mackey-step input selects the branch; the separately supplied foundational
inputs discharge that branch's implication premises.

Finally bundle any datum of the published Proposition 4.8, extract its
auxiliary-place validity, and apply the one-place result. The scalar
tower is already a conjunct of `IsProposition48Datum`; its extraction
does not strengthen the datum. `HasSolution` is exactly the proposition's
four-part output: weak automorphic induction of the original character,
regular algebraicity, conjugate self-duality and supercuspidality at
the specified auxiliary place. The original primary place imposes no
additional output condition and need not be inherited through the
internal induction.

This is a derived organization of M. Harris, *The local Langlands
conjecture for GL(n) over a p-adic field, n < p*, Invent. Math. 134
(1998), 177–210, registered as `harris-1998-local-langlands`,
Proposition 4.8 and proof, printed pp.201–203 (one-based PDF pp.25–27),
companion `math_9611226v1.tex` lines 1554–1674. More precise locators:
Mackey induction, smaller degree and conditions (i)–(iii), 1574–1614;
the general-coefficient Remark, 1616–1628; isobaric Galois invariance,
1630–1644; prime orbit, 1646–1664; singleton and the reference to
Lemma 1.6, 1666–1674. The parity correction is made explicit following
the half-integral-twist Remark on printed p.191, lines 866–875, and the
algebraic normalization on printed p.195. The singleton input records
the local descent, finite-character correction and extension-selection
obligations of Lemma 1.6, printed pp.188–189, lines 687–794.

The one-place strong-induction organization and explicit raw/corrected
realizations are internal interfaces, not extra conclusions attributed
to the source. Lemma 4.7 is used in the arithmetic input's proof, not
assumed anew by this reduction. Its published proof does not by itself
prove the required character and place transports. The general-coefficient
comparison, automorphic constructions and local supercuspidality remain
the explicit inputs above. No `n < p` bound or stronger ramified local
comparison is added, and no published Lean declaration is changed.
