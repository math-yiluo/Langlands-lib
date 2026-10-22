# Normalized induction for actual upper block parabolics

Author: Worker 8.

`Langlands.Parabolic.NormalizedInductionStatement` conjoins four theorem
statements over actual mathematical constructions. The four assertions are
`Prop` definitions, with separate theorem proof obligations.

Fix a prime `p`, a finite extension `F : PadicField p`, a compatible
topological realization `T`, and an ordered positive block shape `B` of
rank `n`. The group is `G = GL_n(F)`, the actual upper block parabolic is
`P = B.parabolic F.Carrier`, and its Levi is the actual product
`M = B.Levi F.Carrier`. The projection is the published diagonal-block map
`q = B.leviProjection F.Carrier`. All group topologies are those supplied by
`T.topology`. The field and the three complex representation carriers
`U`, `V`, `W` have independent universes. No topology or finite dimension is
imposed on a representation carrier.

## Actual normalization

The positive half-character in every clause is exactly
`T.parabolicHalfModulus B`, from `Langlands.Group.GL.BlockModulus`. On a
Levi element `m = (m_i)` its square is the complex image of

`delta_B(m) = product_(i<j) |det m_i|_F^(n_j) / |det m_j|_F^(n_i)`.

Here the absolute value is the published residue-normalized determinant
norm. The half-character is the positive square root, inflated along `q`;
its open kernel is proved in the construction module. The theorem takes no
arbitrary character, modulus, Haar-scaling assertion or induction functor
as a parameter.

For each input `sigma`, the actual representation used in the clauses is
`Induction.smoothInduced P (twist (T.parabolicHalfModulus B) (sigma.comp q))`.
Thus its functions have the covariance

`f(pg) = delta_B(q(p))^(1/2) sigma(q(p)) f(g)`,

and `G` acts by right translation. This is the existing normalized
smooth-induction construction with its explicit character written out.
No second induction constructor is defined here.

The identification of the displayed block product with the determinant of
conjugation on the unipotent Lie algebra, or with Haar scaling on the
radical, is a separate formal theorem obligation. Its elementary
mathematical derivation is that conjugation on the rectangular block
`X_ij` is `X_ij -> m_i X_ij m_j^(-1)`, contributing exactly the factor
displayed above. The normalization in this statement is fixed by that
explicit formula; no unproved identification is used as an input.

## Four assertions

`NormalizedInductionAdmissibilityClause` says that admissibility of
`sigma` implies admissibility of its normalized induction. The imported
`IsAdmissible` includes smoothness and finite-dimensional invariant spaces
for every open subgroup. On these groups the convention agrees with testing
compact open subgroups, using their neighborhood basis and the inclusion
of fixed-vector spaces.

`NormalizedInductionExactnessClause` starts with a short exact sequence of
smooth complex representations of `M`, specified by actual intertwiners
`i` and `q`, their injectivity and surjectivity, and equality of image and
kernel. It inflates their linear maps along the actual projection, twists
both by the positive half-character using `twistIntertwining`, and applies
`smoothInducedMap`. The conclusion consists of all three short-exactness
conditions for those actual maps. Their pointwise formula is
`f(g) -> i(f(g))` or `f(g) -> q(f(g))`. The two local inflation intertwiners
have their equivariance obligations proved by evaluating the given
equivariance at the projection. Admissibility and finite length are not
hypotheses of this clause.

`NormalizedInductionDualityClause` says that the smooth contragredient of
the normalized induction of an admissible `sigma` is equivariantly
linearly isomorphic to normalized induction of the smooth contragredient
of `sigma`. Both induction expressions use the same upper parabolic and
the same positive half-character. The smooth contragredient is the
published smooth-vector submodule of the algebraic dual, not the full dual.
The conclusion is existence of an actual representation equivalence.
It does not select or characterize a canonical equivalence or assume a
pairing.

`NormalizedInductionUnitarityClause` says that if admissible `sigma`
admits a positive definite invariant Hermitian form, then so does its
normalized induction. `IsUnitarizable` is exactly existence of such an
algebraic form, via `InvariantPositiveForm`. Neither a complete Hilbert
space nor a topology on the input or output representation is assumed.
There is no irreducibility conclusion.

## Original sources and derivation

Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, revision April 29, 2019:

- Section 1, p.1, defines positive-half normalized right-translation
  induction and states its admissibility using compactness of `P \ G`.
- Proposition III.1.1, p.2, identifies its contragredient with induction of
  the contragredient from the same parabolic.
- Proposition III.1.2, p.2, states preservation of unitarity.

Those original pages were read. Section 1 assumes admissible inducing
representations; that hypothesis is retained in the first, third and
fourth clauses. Its pairing integrates the pointwise dual pairing over a
good compact subgroup. The analogous integral of the positive invariant
Hermitian form gives the algebraic positive form in the fourth clause;
locally constant compact integration is sufficient, without completing the
representation space. The statement records existence rather than choosing
that integral or its measure.

Bernstein--Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Sections 1.8-1.9, printed pp.444-445 / PDF pp.5-6, defines the
normalized smooth functors and states exactness. Sections 2.1-2.3, printed
p.446 / PDF p.7, gives the reductive parabolic setting and the standard
ordered block realization for `GL_n`. These passages support the second
clause with its smoothness hypotheses and its positive half convention.
The exact maps are the existing postcomposition maps on the function spaces.

This is an explicit specialization from connected reductive groups to
`GL_n` over finite extensions of `Q_p`, with complex coefficients. It makes
no equal-characteristic or general-reductive assertion. The empty block
shape in rank zero is included: its groups and half-character are trivial,
and the clauses reduce to the corresponding identity functor assertions.

Registered sources:

- `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
  Section 1, pp.1-2, especially III.1.1 and III.1.2.
- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  Sections 1.8-1.9, pp.444-445, and 2.1-2.3, p.446.

## Dependencies and remaining obligations

Only the published construction modules `Group.GL.BlockModulus`,
`Representation.Induction.Definitions`,
`Representation.Smooth.Contragredient.Definitions`, and
`Representation.Unitary.Basic` are imported. Their authors retain
construction ownership; this pair reuses their declarations directly.

The four theorem proofs, the formal modulus identification, normalized
Jacquet and reciprocity statements, twist and central-character
compatibilities, refinement transitivity, and opposite-parabolic Jacquet
duality remain separate obligations. This pair does not complete the broad
group-side task.
