# Global coordinates for flat graded lines

This internal extension of `GradedLineFlatLocal` develops the algebra needed
to choose a global coordinate after trivializing the degree of the fibre
coordinate. The base is an arbitrary commutative ring, including the zero
ring. No new external classification theorem is used.

`subsingleton_of_all_maximal_smul_top` proves that a finite module is zero
if its quotient by every maximal-ideal multiple is zero. If its annihilator
were proper, choose a maximal ideal containing it. Determinant Nakayama
produces an annihilator element congruent to one modulo this maximal ideal,
contradicting properness. `le_of_all_maximal_le_sup_smul` applies this to the
finite image in a quotient to detect containment of submodules.

`IsUniversalLine.ker_le_quotient` extends the local universal-line kernel
argument to any maximal quotient. The quotient by the extended ideal is an
algebra over the residue field; the universal property factors its quotient
map through evaluation. A coordinate with zero image therefore vanishes
in that quotient.

`le_powSpan_sup_of_surjective` is the homogeneous spanning argument from
`GradedLineLocal`, with the local residue map replaced by an arbitrary
surjective map to a field. It subtracts a scalar multiple of the appropriate
power of the chosen coordinate and uses the stated kernel containment.

For a finite type graded algebra with no negative components and scalar
degree-zero component, the published finite-generation theorem applies to
each component. If a homogeneous element `x` generates the component of a
positive degree `d`, every graded fibre-line map has a nonzero coefficient
of `X` at `x`: otherwise all elements of that component would have zero
linear coefficient, contrary to the fibre-line spanning condition.
`homog_le_powSpan_of_generator` uses the preceding maximal-fibre
containment test to show that powers of `x` span every component.

`faithfulSMul_of_flat_of_maximal_fibres` records a module step: flatness and
nonvanishing of every maximal fibre imply faithful flatness, and tensoring
detects the zero scalar-multiplication map. Thus scalar action is faithful.
In `aeval_bijective_of_flat_of_generator`, each component of degree `j*d`
is flat as a retract of the flat algebra. Its maximal fibres are nonzero
because the image of `x^j` is a nonzero polynomial. Universal line fibres
provide the necessary kernel containment. Each such component therefore
has faithful scalar action. Projecting a polynomial relation onto degree
`j*d` and using the spanning result forces its coefficient in degree `j`
to vanish. The spanning result also proves surjectivity of evaluation.
This argument retains nilpotent coefficients and works over the zero ring.

`exists_aeval_bijective_of_flat_of_free_degree` starts from an explicit
linear equivalence from `R` to the degree-`d` component, applies it to `1`,
and applies the preceding theorem. `polynomialEquivOfFlatOfFreeDegree`
packages the chosen homogeneous coordinate as an algebra equivalence
`R[X] ≃ₐ[R] A`. The hypotheses require universal graded line fibres over
every field over `R`; a free degree component alone does not assert them.
These are internal consequences of the published grading interfaces,
determinant Nakayama, and Mathlib's faithfully flat module results.
