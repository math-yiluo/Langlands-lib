# Common-closure generation and local-constant uniqueness

The proposition `CommonClosureDegreeZeroGenerationStatement` is a
common-closure version of the degree-zero assertion in Tate (2.3.1).
It ranges over every prime, every finite p-adic field, every finite
intermediate field in the specified algebraic closure, and an independent
representation-carrier universe. All virtual groups are the published
continuous exact Grothendieck groups. Their carrier universe is
`max uF uV`, so the actual finite-index induction preserves it.

The generators are the existing exact inductions of differences of two
continuous character lines from any nested finite intermediate field.
The two characters belong to the same source subgroup, so their
difference has virtual dimension zero. The elementary inclusion of their
integer span in the dimension-zero kernel is proved from the published
dimension formulas. Equality with the whole kernel is a statement only.
It requires an actual generation proof, including the required Weil
representation and Brauer inputs; none is assumed as an instance or axiom.

`NonabelianSystemUniquenessStatement` closes the existing
`NonabelianSystem.Unique F e` predicate over all fields and supplied
reciprocity families. It compares assignments for the same family and
specified closure. It neither selects a family nor asserts existence of
a local-constant system. It makes no comparison across distinct
reciprocity families or closures.

The proof helper `unique_of_commonClosureDegreeZeroGeneration` retains
generation as an explicit premise. For each intermediate field and fixed
additive character and measure, the two assignments give additive maps to
`Additive ℂˣ` through the shared `NonabelianSystem.valueAddHom`. Genuine topological abelianization descent and transport
along the supplied reciprocity component show that rank-one agreement
compares every continuous subgroup character. On an induced difference
of characters, degree-zero induction reduces the comparison to the
source field with its trace-pulled additive character. A regular Haar
measure on that source field is constructed using the published Haar
constructor. Additivity and rank-one agreement give equality there.
The equalizer kernel contains the span of all these generators and hence,
under the premise, the entire dimension-zero kernel. Finally, an arbitrary
virtual class is its degree-zero part plus its integer degree times the
trivial character class. Equality on the trivial character proves equality
on that class. Function extensionality identifies the assignments.
The final theorem applies this reduction uniformly over all fields.

The generation statement is a derived presentation of Tate,
*Number theoretic background*, (2.3.1), printed page 11, retained
Part II PDF page 20. Tate's (2.3.2)–(2.3.3), printed pages 11–12,
PDF pages 20–21, give the corresponding degree-zero uniqueness argument.
The published subgroup model and exact induction implement the finite
extensions inside one closure. This module does not assert their
generation by appeal to a different standalone group without proving
the required comparisons.
Registered source: `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The uniqueness assertion specializes Deligne, *Les constantes des
équations fonctionnelles des fonctions L* (1973), Theorem 4.1,
printed page 535, retained PDF page 35, to the existing four-law
common-closure specification. The exact-sequence, measure, degree-zero
induction and rank-one laws are those already documented in
`NonabelianSystem.md`. The original isomorphism-invariant function across
all sextuples has broader scope; this module asserts only uniqueness
on the fixed field and closure, with the same supplied reciprocity
family. Registered source: `deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The uniqueness reduction is an internal Lean proof of the stated
implication. It supplies neither the unproved generation premise nor
the all-field supercuspidal correspondence.
