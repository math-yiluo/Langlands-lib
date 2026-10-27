# Dual Jacquet exponents and scalar class exponents

Author: Worker 196.

The theorem `Langlands.glDualJacquetClassExponent.{uF,uV}` proves exactly
`Langlands.GLDualJacquetClassExponentStatement.{uF,uV}` from
`Langlands.Representation.Exponents.DualJacquetStatement`. The field and source
carrier universes remain independent. For every supplied p-adic topology,
positive rank, block shape, irreducible admissible source and split-center
character, the theorem proves the equivalence with an actual irreducible
admissible opposite Jacquet subquotient with precisely that scalar character.
The existential constituent has the source carrier universe `uV`.

The helper `classExponent_of_dualExponent` first uses irreducibility to obtain
finite generation of the source over its ambient group algebra. The imported
`Langlands.Parabolic.oppositeJacquetFiniteGeneration` supplies finite generation
of the actual normalized opposite quotient over the Levi group algebra;
`Langlands.Parabolic.isAdmissible_standardOppositeJacquet` supplies admissibility.
The given ordinary dual exponent supplies a nonzero full-dual functional
satisfying the scalar eigen-equation with the same character, through
`Langlands.UnitaryDualJacquetSupport.exists_dualEigenfunctional`. Block scalars
commute with the Levi, and its compact open subgroups are cofinal.

The proof applies
`Langlands.MaximalConeQuotient.exists_irreducible_quotient` to these data.
This imported theorem constructs an irreducible admissible quotient of the
whole opposite Jacquet module with the prescribed scalar character, in the
source carrier universe. Its construction takes the proper invariant orbit kernel of the nonzero
functional and uses finite generation to place that kernel in a maximal
proper invariant subspace. The resulting quotient is simple; central scalar
defects belong to the orbit kernel, so the quotient has the same character. The imported
`Langlands.UnitaryDualJacquetSupport.classExponent_of_quotient` realizes this
quotient as the required subquotient, using the top invariant subspace and its
actual surjective intertwiner. This direction needs no temperedness, unitarity
or positive-rank hypothesis.

The helper `dualExponent_of_classExponent_of_spanning` takes generalized
full-dual spanning indexed by the actual `IsDualJacquetExponent` predicate.
It restricts the supplied full-Levi invariant subspace to the block scalar
group, preserving its underlying submodule. The supplied surjective
intertwiner then satisfies the scalar quotient equation required by
`Langlands.ScalarSubquotientDualSpectrum.scalarSubquotient_mem`.
Irreducibility gives nontriviality of the quotient carrier. The imported
detection proof uses surjective dual restriction and independence of
simultaneous generalized weight spaces to return membership in the indexing
predicate. Here that membership is the full dual-exponent predicate, including
open kernel and a nonzero ordinary exponent-one space. The helper permits an
independent quotient carrier universe.

The closing theorem discharges the spanning hypothesis with the third clause
of `Langlands.glDualJacquetFiniteness`, applied to exactly the given
irreducibility and admissibility hypotheses. This is spanning of the full
algebraic dual by the actual generalized components indexed by smooth ordinary
dual exponents. The proof introduces no finite-dimensionality assumption,
constituent decomposition, quotient map premise or additional theorem-valued
hypothesis. The two helpers then give the two implications of the exact target.

This is a derived algebraic proof of the existing comparison statement.
The original target's source is Silberger, *Introduction to harmonic analysis
on reductive p-adic groups* (1979), Lemmas 3.2.1–3.2.2, Theorem 3.2.4 and
Corollary 3.2.5(1), printed pp.120–123 (PDF pp.126–129), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Worker 196 read the original page images. The implemented route uses dual
spanning rather than the source's matrix coefficient realization. The
normalized opposite Jacquet action and full transpose are the unchanged
Library constructions: the lower (opposite) unipotent coinvariant quotient
is twisted by the positive upper half-modulus, and transposition sends a functional to
its composition with the action. The character is unchanged, with no inversion
or conjugation. No weakly critical, critical/minimal, discrete-series support,
exhaustion, tempered unitarity or genericity result is used.
