# Irreducibility of actual unitary induction from a simple Jacquet module

Author: Worker 480.

This derived supporting construction connects the published normalized-induction
positive form and admissibility theorems to the semisimple-induction
irreducibility argument. It treats actual smooth induction and the actual
normalized same-parabolic Jacquet module. The field/group universe and the
representation carrier universe are independent.

The generic theorem assumes a locally compact Hausdorff nonarchimedean group
with its Borel measurable structure, an actual semidirect decomposition
`P = M ⋉ U`, closedness of `P` and `U`, continuity of the Levi projection,
local compactness of `P`, and compactness of the canonical left-coset quotient
`P \ G`. The ambient modular character is trivial, the full modular character
of `P` equals the restricted Haar modulus of conjugation on `U`, and `U` has
trivial inner-conjugation Haar modulus. The inducing object is admissible and
unitarizable. Its induced same-parabolic Jacquet module is irreducible.

Under these hypotheses, compact-quotient induction preserves admissibility,
and `normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` supplies an
invariant positive form. Compact-open cofinality follows from the ambient
nonarchimedean and local compactness hypotheses. The published
`isIrreducible_induction_of_unitary_irreducible_jacquet` then proves
irreducibility. Its implemented route uses admissible unitary semisimplicity
and first-adjointness naturality to show that every nonzero invariant
projection is the identity.

The transitive adjointness dependencies of this route are
`FirstAdjointness.equiv`, `FirstAdjointness.equiv_ne_zero` and
`FirstAdjointness.equiv_comp`, used in
`induction_idempotent_eq_id_of_irreducible_jacquet`. The semisimplicity
dependency is `Langlands.admissibleUnitarySemisimplicity`, used in
`isIrreducible_induction_of_unitary_irreducible_jacquet`. These are the actual
normalized smooth functors for the displayed decomposition, with independent
group and representation carrier universes. The admissibility dependency is
`normalizedInductionFunctor_obj_isAdmissible`; it uses the displayed continuous
projection and compact quotient.

The rational specialization uses the canonical `pointTopology` on the actual
rational-point group and the literal standard parabolic and Levi subgroups.
It retains connected reductivity, the maximal split torus, a generic
cocharacter, the standard-cocharacter statement, closedness of the parabolic
and unipotent subgroups, and continuity of the actual standard Levi projection.
The inducing object has arbitrary carrier universe `v`; induction has carrier
universe `max u v`.

`DynamicParabolicQuotientCompactStatement` gives compactness of the actual
quotient through `compactSpace_leftQuotient_parabolic`.
`RationalParabolicModulusStatement` gives ambient unimodularity and the full
parabolic modular-character identity. Closedness gives local compactness of
the parabolic. The published compact-limit theorem for the actual standard
unipotent subgroup supplies its inner-conjugation unimodularity through
`standardUnipotent_isUnimodular_of_standardCocharacterStatement`.
The generic theorem applies with no extra compact-open cofinality premise.

`standardUnitaryInductionSubrepresentationEquiv` constructs an actual
representation equivalence from any supplied nonzero invariant subspace of
this rational induction onto the whole induction. Irreducibility makes the
subspace equal to the whole carrier; the equivalence is the actual inclusion,
as its application lemma records.

No cuspidality, maximal-index hypothesis, finite-length hypothesis or
irreducibility of the inducing object is used in these deductions. The
admissibility and unitarizability of that object and irreducibility of the
whole induced Jacquet module remain explicit inputs. In particular, a unitary
central character by itself does not discharge the unitarizability input.
The two named structural statement inputs remain proof obligations.
This supporting construction does not prove
`RationalRankOneSelfAssociationStatement` or alter its published premises.

The provenance is internal and derived from the named published Library
constructions and the invariant-subspace inclusion. The proof uses no
geometric filtration, cuspidal-support theorem, square-integrability criterion,
classification theorem or representation-character independence.
