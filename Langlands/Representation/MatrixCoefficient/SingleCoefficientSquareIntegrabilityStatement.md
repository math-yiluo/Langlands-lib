# Renard IV.3.2: one square-integrable coefficient, without assumed admissibility

Author: Worker 1222. The module
`Langlands.Representation.MatrixCoefficient.SingleCoefficientSquareIntegrabilityStatement`
defines the proposition
`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`.
This is a statement unit; it supplies no proof of the criterion.

## Source and scope

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.3.1 and IV.3.2 Definition and Remark,
printed pp.99–100 / PDF pp.105–106. The registered literature ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passages were read directly, together with II.1.1, printed p.30 /
PDF p.36, for the meaning of a t.d. group.

IV.3 assumes that the t.d. group is unimodular and equips its quotient by its
center with a bi-invariant Haar measure. IV.3.2 defines square-integrability by
a unitary central character and square-integrability of every smooth matrix
coefficient. Its Remark asserts that, for an irreducible smooth representation
with a unitary central character, one nonzero square-integrable coefficient
suffices. It does not assume admissibility. Renard leaves this assertion to the
reader; it is a proof obligation of the whole-book program.

The Lean statement uses the same quotient-measure formulation as the published
IV.3 statements: the specified Haar measure on the actual quotient `G / Z(G)`
must also be right invariant. This records the bi-invariant measure used in the
source, without choosing an auxiliary measure on `G`. The group is Hausdorff,
locally compact and totally disconnected. There is no reductivity, local-field,
countability, finite-length or finite-dimensionality hypothesis. The group
universe `u` and representation-carrier universe `v` are independent, and the
carrier has no topology.

## Exact Lean meaning

For an irreducible `π : SmoothRep.{0, u, v} ℂ G`, the statement quantifies over
the actual datum `c : UnitaryCentralCharacter π.representation`. It consists
of a character of the actual center, its open kernel and unit norm, and the
specified scalar action on every representation vector.

The premise supplies `ℓ : SmoothDual π.representation` and `x : π` such that
the function `matrixCoefficient π.representation ℓ x` on `G` is nonzero and
`MemLp (c.coefficientNorm ℓ x) 2 μ`. Here
`c.coefficientNorm ℓ x` is the well-defined function
`g Z(G) ↦ ‖ℓ (π(g) x)‖` on the actual quotient. The conclusion is
`MemLp (c.coefficientNorm m y) 2 μ` for every smooth functional `m` and vector
`y`, using the same central character and Haar measure. This is the
all-coefficients condition of the source definition.

`MemLp` expresses almost-everywhere strong measurability and finite L²
seminorm. Only the coefficient norm descends to the quotient: a complex
coefficient need not do so when the central character is nontrivial.

## Relation to the published admissible criterion

The existing proposition
`Langlands.Renard.CompactRepresentation.SquareIntegrableCoefficientCriterionStatement`
and its theorem `squareIntegrableCoefficientCriterion` remain unchanged.
They assume admissibility and conclude `IsSquareIntegrableModCenter`, the
published Casselman-style predicate that includes admissibility.

The new proposition exposes the broader source obligation. Its conclusion is
written out as the all-coefficients condition, so it neither assumes
admissibility nor hides it inside the premise. The existing proof uses
admissibility to obtain irreducibility of the smooth dual before spanning that
dual by translates of `ℓ`; it does not prove this new proposition.

After the new criterion is proved, the published
`essentiallySquareIntegrableAdmissible` theorem can be applied with the trivial
twist to deduce admissibility. The all-coefficients conclusion can then be
packaged as `IsSquareIntegrableModCenter`. This is a consequence to derive,
not an assumed admissibility input or a proof supplied by this module.
The general t.d.-group obligation cannot be discharged merely by invoking
admissibility of irreducibles of reductive local-field groups.

## Dependencies and remaining work

The statement imports the existing smooth representation category and the
actual central-character and quotient-norm construction by Lean module name.
It introduces no replacement representation, dual, quotient or predicate.
Independent review and publication of this statement, followed by an exact
proof in a separate proof task, remain required. This statement alone does not
close clarification C3 in the Chapter IV item ledger or complete Chapter IV.
