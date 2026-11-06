# Cuspidal coefficient norms on the full central quotient

`Langlands.HasCompactUnitaryCoefficientsModCenter` is the property that, for
every prescribed unitary central character, every smooth algebraic-dual
functional and every representation vector, the descended coefficient norm
has compact support on the quotient by the full abstract group center.
It asserts neither existence of a unitary central character nor smoothness,
irreducibility or admissibility of the representation.

`compactUnitaryCoefficients_centerQuotient_of_isCuspidal` proves this property
for a smooth complex representation of the actual rational-point group of a
connected reductive group over a nonarchimedean local field. The field and
representation carrier have independent universes. The rational-point topology
is canonical, with local compactness, nonarchimedean group structure and
Hausdorffness assumed. The theorem retains a maximal split torus embedding, a
generic cocharacter, `StandardCocharacterStatement`, a relative root system,
closed actual standard unipotent subgroups, and a specified compact subgroup
with `SimultaneousStandardBasisAt` and `FiniteCartanCovering`. Cuspidality means
vanishing of all proper normalized standard Jacquet modules.

The proof applies
`hasCompactSupport_centerQuotient_of_finiteCartanCovering` to the descended
coefficient norm. For each finite set of centralizer factors,
`exists_rational_compact_translate_pairing_bound` gives a single upper bound on
all simple-root coordinates of nonzero coefficients after both compact
translates. The lower bound is dominance in the literal Cartan cover. The
identity `UnitaryCentralCharacter.coefficientNorm_mk` and nonvanishing of a
norm identify the nonzero loci on rational points. The support theorem then
uses the already proved simple-root detection modulo the full center and a
compact product of finitely many quotient classes. This includes the closure
of the nonzero locus; no continuity hypothesis on the coefficient norm is
needed for that support argument.

This is derived internal assembly of the imported results, motivated by the
forward implication of Renard VI.2.1. It is a supporting theorem with explicit
geometry. It does not prove the structural existence statements or compare
the actual represented-parabolic cuspidality hypothesis with the standard
family, and does not claim the unrestricted
`SupercuspidalUnitaryCoefficientCompactSupportStatement`.
