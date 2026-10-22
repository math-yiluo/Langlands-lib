# Standard Whittaker characters and models on GL

Author: Worker 31. This module consumes Worker 6's actual upper-unipotent matrix subgroup
and Worker 20's shared additive-character construction. Those source modules
remain their contributions.

For positive rank written `n + 1`, the standard character is the composite of
the homomorphism summing first-superdiagonal entries, the supplied unitary
additive character, and Mathlib's map from the unit circle to complex units.
All group laws come from these proved homomorphisms. Its value is
`ψ(∑ i, u[i,i+1])`, equivalent to the product in JPSS because ψ is an additive
character. The module proves that the values have norm one. It also constructs
the inverse character for the second member of a JPSS pair and the character
obtained by replacing ψ(x) by ψ(a*x), for a specified unit `a : Fˣ` (a nonzero
element when F is a field).
No second additive-character type is introduced.

Rank one is included: the first-superdiagonal sum is empty and its character is
the trivial character. Every linear form satisfies its unipotent condition:
an upper-unipotent matrix in rank one is the identity. Continuity of the standard,
inverse and scaled characters follows by composing the continuous entry-sum
map with the shared continuous character and checking both coordinates of the
complex-unit topology. Scaling by `-1` is proved to give the inverse character.
The standard, inverse and scaled characters need only a commutative ring
with a topology; `IsTopologicalRing F` is assumed only for their continuity
constructions and the model regularity results. Representation coefficients are complex numbers,
with independent universes for the field and representation carrier.

The functional space and coefficient model specialize the actual Algebraic
construction, rather than introducing another representation hierarchy.
Model vectors evaluate to complex-valued functions, with the required left
unipotent covariance and right-translation action. A specified nonzero functional
on an irreducible representation gives the previously constructed representation
equivalence onto its actual coefficient image.

`IsGeneric` is the conjunction of irreducibility, the accepted admissibility
predicate (which includes smoothness), and existence of a nonzero standard
Whittaker functional. This is an existence predicate, not a proof of
multiplicity one. No one-dimensionality or choice of a preferred functional is
asserted. The usual source equivalence with the dimension-one formulation for
irreducible admissible representations requires the separate multiplicity-one
theorem.

Local constancy of each model function is the published theorem
`Langlands.matrixCoefficient_isLocallyConstant` (Worker 0's matrix-coefficient
laws in `Langlands.Representation.MatrixCoefficient.LawsProof`). It is applied to
a preimage of the model vector under the surjective coefficient map, so every
model function is locally constant, hence continuous. No topology or continuity
hypothesis on the representation space or linear functional is used.

Original source: Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, notation p.377 (right translations and θ), §2.1 pp.385–386
(functionals, genericity and coefficient-image model).
Registered source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original printed pp.377 and 385 were reread directly while preparing this
specialization; the coefficient-image construction was checked against p.386
in the Algebraic contribution.

The imports `Langlands.Group.GL.UpperUnipotent`,
`Langlands.HarmonicAnalysis.Basic`,
`Langlands.Representation.MatrixCoefficient.LawsProof`, and
`Langlands.Representation.Whittaker.Algebraic` are published Library modules.
Their published Lean sources were compared with the sources used for native
compilation and are unchanged. This pair imports those constructions by Lean
name and republishes none of their implementation. The module compiled without
diagnostics in the pinned environment. Compilation is development evidence;
independent review and publication of this pair remain required.

This construction supplies the characters and models used by JPSS integrals.
Analytic continuation, multiplicity one, the integral constructions and factor
existence require separate work.
