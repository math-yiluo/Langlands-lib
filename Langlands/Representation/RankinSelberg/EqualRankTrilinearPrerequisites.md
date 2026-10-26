# Equal-rank uniqueness from the named prerequisites

This internal adapter assembles the named prerequisite statements into the
unchanged `EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n`. It is
conditional: GL finite length, mirabolic restriction finite length,
irreducible functional multiplicity, twisted-pairing rigidity, the compact
twisted pairing and Frobenius reciprocity remain explicit premises. The
central bilinear step uses the published `centralBilinearVanishing` proof.
The adapter proves none of its input premises and supplies no unconditional
proof of the parent target.

`EqualRankTrilinearPrerequisites` is an internal Prop-valued definition,
the conjunction of those nine named inputs: GL finite length and mirabolic
restriction finite length in each carrier universe, functional multiplicity
in each carrier universe, pairing rigidity, compact pairing and Frobenius.
The final assembly theorem takes this bundle and immediately unpacks all
nine proofs. The bundle is not assumed to hold and contains no conclusion
of uniqueness.

Worker 353 authored the assembly. Workers 440 and 501 supplied the pairing
and Frobenius interface drafts used during its development. The module now
imports their published statements unchanged, together with the published
finite-filtration, source-reduction, character-change and normalization
helpers. It includes no copied statement pair or private mathematical input.

## Irreducible-pair control

`mirabolic_pair_control_of_statements` converts the irreducible functional
and pairing statements into the precise pair-control premise of the published
finite-filtration bound. A nonzero extended-natural length of the actual form
space gives a nonzero form. Rigidity identifies both irreducibles with the
actual compact model. Functional multiplicity then supplies one-dimensional
functional spaces on both. Transporting the bilinear space through the two
representation equivalences and the flip equivalence identifies its length
with the compact pairing's length, which is one. If its length is zero the
bound is immediate. The finite exceptional set precedes the exponent and
every form. No finite `finrank` stands for a potentially infinite dimension.

## Source and coefficient-model assembly

`equalRankTrilinearUniqueness_of_prerequisites` handles arbitrary
Whittaker-type source representations. The published character-change
functional equivalence for the diagonal with alternating signs changes the
second representation's inverse character to the first character without
changing its carrier or action. The published identity
`standardCharacter_scale_neg_one`, imported from `FunctionalEquationStatement`,
identifies the scaled character with the inverse character. Thus the same positive-character functional criterion applies
to both filtrations. All three universes remain independent.

The supplied topology is compared with the canonical module topology by
`TopologicalData.topology_eq_canonicalModule` before applying each GL
finite-length premise. Restriction finite length then applies to the actual
mirabolic actions. The published mirabolic finite-filtration bound and
spectral translation supply the weight `1-s`. Frobenius and the published
central bilinear vanishing theorem give source uniqueness through the
existing actual row-Schwartz assembly. Coefficient-model descent then gives
the exact target, including arbitrary and zero functionals, with one
exceptional set before all exponents and forms.

This is internal derived mathematics proving compatibility of named Library
interfaces. Its route implements the finite-filtration and residual-central
structure of JPSS (1983), Section 2.10, printed pp.396–398, through the
previously published assembly lemmas. It makes no new source-derived claim
and leaves all representation-theoretic input proofs as explicit premises.
