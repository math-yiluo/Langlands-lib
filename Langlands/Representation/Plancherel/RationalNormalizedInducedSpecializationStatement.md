# Renard VI.8.2: specialization of actual normalized induction

Worker 1759. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 version, VI.8.2, base-change proposition and formula
(VI.8.2.2), printed p.190 / PDF p.196, and specialization corollary, printed
p.191 / PDF p.197. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`RationalNormalizedInducedSpecializationStatement` asserts bijectivity of the
constructed complex-linear `inducedScalarExtension`. This is a statement and
necessary construction; no fiber bijectivity proof is supplied.

The coefficient ring is exactly the published `RegularAlgebra r`, the concrete
regular-function algebra for the norms of **all** rational characters of the
actual Levi. For every actual unramified character χ, its homomorphism to ℂ is
`evaluation r χ`, and `InducedSpecializationFiber` is the literal tensor
`ℂ ⊗[B] Induced r h hU π.representation` with B acting on ℂ through this
evaluation. The target is the published `complexInduced r h hU π χ`, exactly
the existing normalized induction functor applied to the unramified twist of π.
The source uses the factors in the order `Induced ⊗[B] ℂ`; the displayed fiber
uses the canonical commutation of tensor factors.

The generic helper `scalarExtensionOfSemilinear` extends any semilinear map
`T : V →ₛₗ[algebraMap R S] W` to `S ⊗[R] V →ₗ[S] W`. It uses the tensor
universal property on the bilinear map `(z,v) ↦ z • T v`; tensor induction
proves S-linearity. This is the elementary scalar-extension construction,
not an assumption about the representation. Applying it to the existing
semilinear `inducedEvaluation` gives `inducedScalarExtension`, with the proved
pure-tensor formula
`z ⊗ f ↦ z • inducedEvaluation r h hU π χ f`.
The already published `inducedEvaluation_eval` identifies the latter map at
an actual group point g with evaluation at χ of the tensor-valued function
f(g). This is the specialization of the source's formula (VI.8.2.2).
The full normalized induced function space, its covariance, its uniform open
right stabilizer and the positive full-parabolic half-modulus are preserved;
no compactly supported substitute or matrix model is introduced.

The quantified statement ranges over arbitrary connected reductive group
schemes over arbitrary nonarchimedean local fields, actual maps p, l and a
with a `ParabolicRootPresentation`, and the actual unipotent subgroup specified
by n. The representation-carrier universe `uV` is independent of the field and
group universe `u`. π is any smooth complex Levi representation; neither
admissibility nor finite dimension is needed for this specialization claim,
so it applies in particular to the admissible representations of the task.
No flatness, projectivity, fixed-space comparison or specialization bijectivity
is present among the hypotheses.

Retained structural hypotheses are affineness of the supplied Levi, local
compactness and nonarchimedeanness of the canonical rational-point topology,
closedness of the literal unipotent subgroup, continuity of the actual
semidirect projection, and compactness of the literal left quotient P(F)\G(F).
The last two are explicit actual-group propositions. This module does not
claim to derive these structural facts or the existence of the supplied
presentation from connected reductivity. They replace the source's implicit
structural facts about an actual rational parabolic without restricting G
to a split or matrix group.

The source's proof uses the finite compact-open double-coset invariant
comparison and then shrinks the stabilizer. The bijectivity target here
retains that proof obligation for the actual constructed map. Flatness and
compact-open fixed finite projectivity are separate statement units; VI.8.3
and all subsequent Jacquet and generic-irreducibility assertions are outside
this module.
