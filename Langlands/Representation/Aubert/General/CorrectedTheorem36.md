# Corrected Theorem 3.6 on the full smooth support category

Statement target by Worker 194, using Worker 379's support-category definition
and Worker 23's actual normalized functor adapters.

`Langlands.Aubert.General.CorrectedTheorem36Statement` is a proposition target
for the actual complex. Fix standard-subset families `P`, `M`, `U`, their
semidirect decompositions, closed radicals, unimodularity proofs, increasing
parabolics and decreasing radicals, and the endpoint identities
`P(S) = G`, `U(S) = 1`. Also fix the Weyl-association relation, the support
subset `I`, closedness of `M(I)`, and the Levi-in-Levi decompositions used to
define cuspidality. The proposition asserts:

For **every smooth** complex representation `E` of `G`, membership in
`IsInSupportCategory ... I ... E` implies
`StandardComplex.IsExactBeforeTerminal ... E I`.

There is no finite-length, admissibility or irreducibility premise on `E`.
The support predicate constrains its actual irreducible subquotients through
actual normalized cuspidal induction and conjugation. The quantification
over the fixed carrier universe is arbitrary.

The conclusion uses the actual signed differential and its actual incoming
images, not chosen maps between isomorphic graded objects. Removed-root
degree zero is canonically `E` under the supplied endpoints, by
`StandardComplex.initialEquiv`; for a positive terminal degree the first
arrow from `E` is injective by
`StandardComplex.initialDifferential_injective_of_exact`. Exactness is
required only at degrees strictly below `|S| - |I|`. At that degree,
`StandardComplex.terminalProjection` has incoming-image kernel and is
surjective onto the constructed `StandardComplex.sharpObject ... E I`.
These two quotient laws are proved in `StandardExactness`. There is no
condition forcing this retained cokernel to vanish. If `I = S`, including
an empty root set, there are no earlier degrees to check.

## Source and proof boundary

The exact source target is the theorem in Aubert's 1996 erratum, printed
p.4687, display (*), with its definition of `Alg({I})` immediately above.
The cokernel is defined on printed p.4690. The theorem is still a target:
the actual group must instantiate the subgroup and association parameters
through the shared Renard framework. The definition does not assert that
all generic nested families satisfy it.

Its proof must use the two-sided Bruhat supports and prior double-coset
minimality of Ban–Jantzen 2016, Section 4, printed pp.161–162, together with
the required actual geometric-lemma comparisons, signed graded-transition
squares, termwise exactness and support-theory detection. A finite Weyl
filtration does not impose finite length on `E`, and induction on
composition length alone would not prove this target.

Proposition 3.2 remains unresolved. Aubert 1995, p.2187, contains the false
homogeneous-space identification in its proof; the original Theorem 3.6
proof on p.2188 uses that proposition and is not evidence. The erratum's
left-saturated supports on pp.4687–4689 must be replaced by the largest
two-sided invariant subsets before using its geometric-lemma calculation.
The Ban–Jantzen p.161 comparison is between consecutive modified supports,
and its p.160 wording about a complex ending in zero must retain the terminal
homology.

Intrinsic quotient, sign and naturality laws are construction results.
The corrected exactness assertion is a representation-theoretic proof
obligation; it is not an allowed external Chapter V structural assumption.
The proposition has no classification premise. Its transitive module imports
do reach classification modules; this is not a classification-independence
claim. Any subsequent proof using the formal duality identities through
Ban–Jantzen Proposition 4.1(3), p.158, must record that passage's
Langlands-classification dependency.
