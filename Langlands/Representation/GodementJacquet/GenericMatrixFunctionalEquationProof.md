# Normalized matrix functional-equation data for the actual representation

`Langlands.GodementJacquet.genericMatrixFunctionalEquation` has exactly the
unchanged `GenericMatrixFunctionalEquationStatement.{uF,uV}` as its type.
The implementation applies `genericMatrixFunctionalEquationReduction` to the
closed `tateMatrixFunctionalEquation` and
`supercuspidalMatrixFunctionalEquation` theorems, with the same independent
field and carrier universe parameters. Neither analytic base remains a premise
of the theorem being proved.

The reduction derives the scalar central quasicharacters of the actual
irreducible supercuspidal factors from admissible Schur, and embeds the actual
input representation into their canonical normalized product by the published
classification theorem. The two analytic theorems supply full normalized data
on every positive-rank factor: Tate treats rank one, and the supercuspidal base
treats rank at least two with both denominator polynomials equal to one. Finite
product induction constructs full ambient matrix data. Restriction to the
actual image of the injection and the inverse of the range equivalence give
a surjective intertwiner onto the original representation. Actual-subquotient
descent constructs its normalized polynomials, complex unit and integer.

The original Whittaker-type certificate supplies admissibility and smoothness;
irreducibility supplies nontriviality of the actual carrier. No chosen model,
central-character certificate, analytic assertion, generator, or selected
factor is an extra premise. The conclusion is full normalized matrix data on
the supplied representation itself, including rank one and an arbitrary
carrier universe independent of the field.

All analytic content is inherited through the unchanged data predicates and
theorems. The common convergence half-planes, actual rational continuations,
both normalized Laurent-span generators with constant coefficient one,
Fourier witnesses chosen before coefficients, and guarded equation for every
actual continuation pair remain present. The supplied scalar self-dual Haar
measure is retained, including its square matrix product. The Fourier pairing
uses the plus transpose convention and the coefficient uses inverse transpose.
The normalized shifts, variable `q^(-s)`, central scalar one and sign exponent
zero are unchanged.

This module is an internal composition of the imported analytic and structural
proofs. Godement and Jacquet, *Zeta Functions of Simple Algebras* (1972),
Theorem 3.3 and normalization discussion, printed pages 30–34 (PDF pages
40–44), provide the original admissible irreducible assertion and normalized
generators. The registered source is
`godement-jacquet-1972-zeta-simple-algebras`, SHA256
`86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`.
The plus transpose formulation is the adaptation in Jacquet,
Piatetski-Shapiro and Shalika, *Automorphic Forms on GL(3) I* (1979),
printed page 177 (PDF page 10), equations (1.1.1)–(1.1.2), registered as
`jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
These original normalization passages were read during development. The
imported proof pairs describe their implemented analytic arguments; this
composition makes no assertion of unconditional existence on arbitrary
reducible representations.
