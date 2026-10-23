# Weakly critical discrete-series support and pair minimality

Author: Worker 19.

These proposition definitions refine the existing discrete-series support
existence statement by retaining a prescribed weakly critical exponent. They
also state existence of a weakly minimal standard pair and the converse from
criticality to minimality. They prove none of these representation-theoretic
assertions.

The field `F : PadicField p` and representation carrier have independent
universes `uF` and `uV`. The rank is positive, the source `A` is irreducible, and
`T.IsTempered A.ρ` is the Library's analytic temperedness modulo the full
center. It includes admissibility and smoothness. All exponents and their
indices come from the full transpose dual of the actual normalized opposite
Jacquet quotient. Their unitary spectrum is compared with the source's weak
exponents by the separate DualJacquetStatement family.

`GLWeaklyMinimalStandardPairExistenceStatement` asserts that some standard
block pair has a nonempty unitary dual spectrum and that no strictly finer
concrete pair has one. Its minimality condition tests every conjugate block
pair, including nonstandard ones, through actual subgroup inclusions.

`GLWeaklyCriticalDiscreteSeriesSupportStatement` takes any standard block
shape `B` and any prescribed weakly critical exponent `χ`. It provides an
irreducible admissible representation `S` of the actual product Levi that
occurs as an opposite Jacquet subquotient, has scalar split-center character
exactly `χ`, is square-integrable modulo the full Levi center, and has an
injective intertwiner from `A` to its normalized opposite parabolic induction.
Square-integrability quantifies over all Borel Haar measures on that actual
central quotient. This uses the genuine unitary discrete-series predicate,
not essential square-integrability after an unspecified twist. The
existential carrier is in `uV`, as in the published support family: `S` can
be realized on a quotient of a subspace of the actual Jacquet module. It is
not required to use the same vector space as `A`.

The opposite induction has right translation and positive half of the
opposite modulus in its covariance, that is, inverse upper half-modulus.
The normalized opposite Jacquet action instead multiplies by the positive
upper half-modulus. Its transpose dual therefore has source-functional
eigenvalue equal to inverse upper half-modulus times `χ`, with no inversion
or conjugation of the character. Criticality tests the strict inequality of
uniform nilpotence indices for every extending unitary exponent at every
proper finer pair. None of these conditions is replaced by a multiplicity
count or an absence-of-exponents definition.

`GLWeaklyCriticalPairMinimalityStatement` asserts the equivalence of the two
distinct predicates for every concrete conjugate pair. Existence of a
critical exponent is enough; it is not assumed that all exponents are
critical. The minimal-to-critical direction already has an intrinsic proof
in WeakCritical. The critical-to-minimal direction is the substantive source
conclusion, here only stated. The conjunction entry is
`GLWeaklyCriticalTemperedRefinementStatement`.

The original source is A. J. Silberger, *Introduction to harmonic analysis on
reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis`, retained SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The paragraph before Corollary 4.5.11 on printed p.189 (PDF p.195) supplies
the definitions and existence of minimal pairs. Section 0.3, pp.5–6
(PDF pp.11–12), supplies standard-pair conjugacy, used to select a standard
minimal pair. Corollary 4.5.11 on pp.189–190 (PDF pp.195–196) supplies the
prescribed-character discrete-series support. Its proof first uses
Corollary 4.5.7 to obtain an opposite Jacquet class exponent with that
character and then shows it is discrete series. Corollary 4.5.12(3) on
p.190 supplies critical-to-minimal under existence of a discrete-series
class exponent. Corollary 4.5.11 provides that existence, so the statement
here does not repeat it as a premise. The formula-bearing pages were read
as original images.

This is a derived specialization to `GL_n` using every concrete conjugate
block pair for refinement and minimality. The support assertion retains the
source's standard-pair formulation. The analytic `L²` and `L^(2+ε)` predicates
and the unitary dual spectrum translate the source's representation classes
through the separately stated exponent criteria and class comparisons.
Neither those comparison proofs nor a formal proof of the algebraic-group
conjugacy/exhaustion theorem is supplied here. This family does not assert
the Weyl-conjugacy conclusions of Corollary 4.5.12(1)–(2), semistandard
recovery, a general reductive version, or any new proof of the Langlands
quotient theorem.
