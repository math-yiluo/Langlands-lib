# The PQ-regular intertwining characterization (Renard VII.3.4)

Author: Worker 154. Module
`Langlands.Representation.Intertwining.PQIntertwiningOperatorProof`.

The theorem
`Langlands.Aubert.General.RepresentedParabolic.pqIntertwiningOperator`
has exactly the published type `PQIntertwiningOperatorStatement.{u, v}`.
It proves existence and uniqueness for every supplied equivariant identification
of the identity support subquotient with the smooth representation `σ`, with
independent field and representation universes and no additional hypothesis.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VII.3.4, printed pp.235–236 / PDF pp.241–242; the regularity
ideals are in VII.3.3, printed pp.233–234 / PDF pp.239–240. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read PDF pp.240–242. This is a proof of the derived published
characterization. The identification `e` remains supplied, as in that statement;
the theorem does not construct the Haar integral identifying the subquotient.

## Implemented proof

The proof first establishes a general extension lemma for complex group
representations. Let `ρ` and `σ` be representations of a group `H`, let
`φ : B → H` have central image with `B` commutative, and let `T` be a
subrepresentation of `ρ`. Suppose the action kernels on `σ` and on `ρ/T`
sum to the whole algebra `ℂ[B]`. Write `1 = a + b`, with `a` in the first
kernel and `b` in the second. The action of `b` is the identity on `σ` and
maps `ρ` into `T`. Its action is `H`-equivariant because `φ` is central.
For any equivariant map `q : T → σ`, the formula `K(x) = q(bx)` therefore
extends `q`. For any competing extension `L`, equivariance extended linearly
to `ℂ[B]` gives `L(x) = L(bx) = q(bx)`, proving uniqueness. The helper
`intertwining_groupAlgebra_apply` and the equivariance of
`centralGroupAlgebraAction` use linear induction on the monoid algebra.
The theorem `existsUnique_intertwining_extension` implements this argument.

For the exact specialization, `ρ` is `r_Q^G i_P^G(σ)`, `T` is the value of
`boundarySupportImage` at the identity double coset, and `q` is the quotient
projection followed by the supplied identification `e`. `IsPQRegular` is
exactly the required sum-of-kernels equality, and the split-component
hypothesis supplies centrality of `φ = rationalPoints.map a`.

The published theorem `leviFrobeniusReciprocity` identifies the intertwiner
space into `i_Q^G(σ)` with equivariant maps from `r_Q^G i_P^G(σ)` to `σ`.
Its explicit identity-evaluation formula transfers the constructed `K` to
the required `J`. For uniqueness, every vector in the boundary support image
has a representative `f` in the boundary vanishing subspace, directly by
the image definition. Thus a competing intertwiner satisfies the extension
property on every vector of `T`; uniqueness of `K` and injectivity of the
Frobenius equivalence give uniqueness of `J`.

## Dependencies

The module imports the unchanged target statement and
`Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof`.
The proof uses no support-graded or regularity-lemma theorem from VII.3.2–VII.3.3:
the sum-of-kernels definition and the supplied `e` suffice. All mathematical
helpers are in this paired module. The original statement and its imported
Lean/Markdown pairs are unchanged.
