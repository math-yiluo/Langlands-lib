# Smooth extension of bounded intertwiners along a split restriction

Let real Lie groups \(G\) and \(A\), modeled on real normed spaces, act by
bounded operators on complex normed spaces \(E\) and \(H\), respectively.
Suppose there are homomorphisms \(i\colon G\to A\) and \(p\colon A\to G\)
and a map \(c\colon A\to A\) with \(a=c(a)i(p(a))\), where \(c(a)\) commutes
with \(i(G)\). Both \(p\) and \(c\) are smooth.

The proposition `SmoothIntertwinerExtensionStatement` assumes that evaluation
at a locally smooth vector \(x_0\in E\) on the bounded intertwiner space
for the restriction along \(i\) has a bounded complex-linear left inverse
defined on \(H\). For each such intertwiner \(T\) with globally smooth
\(Tx_0\), it gives a continuous complex-linear map from the local smooth
vectors to the global smooth vectors, both in their genuine word-derivative
topologies. Its value at \(v\) has underlying vector \(Tv\).

Apply the left inverse to the orbit of \(Tx_0\) along \(c\). This recovers
the operator \(\sigma(c(a))T\) and makes the operator family smooth in norm.
Applying this family to the local orbit along \(p\) gives the global orbit
of the image of any local smooth vector. The product and chain rules at
the identity express one global derivative as the sum of the derivative
of the operator family applied to \(v\) and \(T\) applied to the local
derivative along \(dp\). The derivative of the operator family lies in the
same intertwiner space. At \(x_0\), the product identity expresses its
value as the difference of two globally smooth vectors. Induction by
appending the innermost Lie direction now gives continuity in every global
derivative coordinate. The induced topology gives `derivativeMap`.

The smooth map intertwines the local action and the global action
restricted along \(i\). Consequently a continuous global Whittaker
functional pulls back to a continuous local one when the supplied map
of subgroups agrees with \(i\), with character pulled back along the
subgroup map.

This internal argument uses the Library's bounded intertwiner submodule
and word-derivative topology, and Mathlib's manifold chain and product rules.
