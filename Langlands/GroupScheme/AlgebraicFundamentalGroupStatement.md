# Structure and canonical comparisons for the algebraic fundamental group

These two Prop-valued declarations state the structural and comparison assertions
of Kaletha–Prasad (2023), Construction 11.3.1 and Definition 11.3.2, printed p. 427
(PDF p. 458). The November 2024 corrections leave them unchanged.

`AlgebraicFundamentalGroupStructureStatement` quantifies over every field, every
separable closure, every connected reductive group scheme and every `Choice`.
It states that the actual preimage inclusion is a maximal torus, that its
cocharacter map into the chosen torus lattice is injective, and that the actual
image quotient is finitely generated. The source also identifies the image with
the coroot lattice; this declaration does not claim that additional identification.

`AlgebraicFundamentalGroupComparisonStatement` has the same field and group
scope. For every two choices it asserts unique existence of a map induced by
actual geometric conjugation and that the epsilon-selected comparison has that
property, is bijective and commutes with every element of the absolute Galois
group. For every conjugating geometric point and its restricted torus isomorphism,
the same comparison has the indicated action on representatives. It also asserts
the identity law and the law that composing two comparisons gives the comparison
between their endpoints. Thus it gives canonical Galois-equivariant linear
isomorphisms, even when both the torus and the representative of the simply
connected derived cover vary.

These unconditional targets justify representing Definition 11.3.2 by a chosen
quotient. They assume no comparison-existence or comparison-independence theorem.
Both are statements with proofs left open; the helper theorems in the construction
module prove only the elementary construction and descent facts they name.
