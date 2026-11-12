# Renard III.1.14–III.1.15: coinvariants, Hecke tensors and character twists

Author: Worker 139. The entry theorem
`Langlands.Renard.Smooth.renardCoinvariantTensorStatements` has exactly the
published type `Langlands.Renard.Smooth.RenardCoinvariantTensorStatements`.
Its independent universe parameters u and v correspond to the statement's
u' and v'. No hypothesis is added. The statement's Lean/Markdown pair and all
its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition of 9 July 2026, III.1.14–III.1.15, printed pp.66–69 / PDF
pp.72–75 (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The checked action uses the anti-involution of II.3.12, printed p.52 / PDF
p.58, with the inverted-measure convention of II.3.7, printed p.47 / PDF p.53.

Four focused proof modules provide these components:

| Exact statement | Implemented proof |
| --- | --- |
| `TensorProductSmoothStatement` | `tensorProductSmooth` applies the published `TensorHom.tensor_smooth`: pure tensors are fixed by intersections of open stabilizers, and sums remain smooth. |
| `CheckRightActionExistsStatement` | `checkRightActionExists` constructs the inverted-measure integrated action. Scalar evaluation and compact-support Fubini prove reversed convolution, hence the opposite Hecke-algebra action laws. |
| `CoinvariantHeckeTensorStatement` | `coinvariantHeckeTensor` proves diagonal invariance equivalent to Hecke balancing, supplies complex scalars on the original integer tensor quotient using local units, and constructs inverse quotient maps with the prescribed pure-tensor formula. |
| `TwistEquivalenceStatement` | `twistEquivalence` constructs natural cancellation isomorphisms for character twists, then obtains both adjunctions from the resulting equivalence and its symmetric equivalence. |

The companion Markdown files explain these proofs in detail. This module
proves the remaining associativity assertion and assembles the conjunction.

`CoinvariantTensor.coinvariantsEquiv` is an internal functorial construction:
an equivariant complex linear equivalence e induces maps on coinvariants by
`Representation.Coinvariants.map`. The inverse equivalence induces the inverse
map. Surjectivity of each quotient map reduces the two inverse identities to
those for e. The resulting map sends the class of x to the class of e(x).

`heckeTensorAssociativity` applies `coinvariantHeckeTensor` to the two pairs
`(ρ ⊗ σ, τ)` and `(ρ, σ ⊗ τ)`. Mathlib's
`Representation.TensorProduct.assoc ρ σ τ` is an equivariant equivalence
between their triple complex tensor representations. Descending it by
`coinvariantsEquiv` and composing with the inverse left comparison and forward
right comparison gives the additive Hecke tensor equivalence. Its pure-tensor
formula follows by the comparison formulas and the ordinary associator's
formula `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. This implements precisely Renard's argument
on printed p.69, equation III.1.15.1. The proof uses the published smoothness
hypotheses for ρ, τ, ρ ⊗ σ and σ ⊗ τ, without adding a separate hypothesis on σ.

Finally, `renardCoinvariantTensorStatements` pairs the five exact component
theorems in the published conjunction's order. The claims are on arbitrary
Hausdorff locally compact nonarchimedean groups, including nonunimodular ones,
and on arbitrary complex representation carriers in the stated universe.
There is no admissibility, finite-dimensionality or smallness hypothesis.
The twist assertion covers the four equivalence and adjunction claims of
Remark 3; the source's further preservation and exactness consequences are
not separate claims of this target.
