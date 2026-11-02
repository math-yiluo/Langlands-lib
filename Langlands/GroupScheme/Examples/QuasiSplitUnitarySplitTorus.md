# A rank-two split torus after extending the quasi-split unitary group

Worker 1225. This internal proof unit establishes the third conjunct of the published `QuasiSplitUnitary.RankStatement`.

For an injective weight vector, a block Levi matrix is diagonal. An invertible diagonal matrix has unit diagonal entries, so its matrix group is naturally isomorphic to a family of units. This natural equivalence of points identifies the published block Levi scheme with the split torus indexed by the universe lift of the matrix index type. The block Levi inclusion is a closed immersion by `CorepresentedClosedSubgroup`.

For the two weights `(1,-1)`, the index type has cardinality two. Composing its diagonal torus inclusion with the inverse of the published `splittingIso` gives the required closed split torus in `baseChangeGroupScheme b c`. The argument uses no assumption on the characteristic. These helpers are derived from the published explicit matrix and split torus definitions; they do not assert an upper bound on the rank after base change.
