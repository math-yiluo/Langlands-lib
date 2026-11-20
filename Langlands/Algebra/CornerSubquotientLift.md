# Lifting a fixed-part subquotient

Let \(M\) and \(Q\) be modules over a ring \(R\), with \(Q\) simple, and let
\(e \in R\) be idempotent. Suppose some \(eRe\)-submodule \(P\) of \(eM\)
has a nonzero \(eRe\)-linear map \(q : P \to eQ\). Then \(Q\) is the
quotient of an actual \(R\)-submodule of \(M\).

`fixedGraphMap` takes the graph inside the \(e\)-fixed part of \(M \times Q\).
`generatedFixedGraph` takes its \(R\)-span using the existing `fromFixed`
construction. Projecting this span by \(e\) lands back in the original graph.
Suppose \((0,z)\) lies in the span. Each \(ea(0,z)\) lies in the graph, so
its second coordinate vanishes. If \(z \ne 0\), simplicity gives an \(a\)
with \(az\) a chosen nonzero value of \(q\). This is fixed by \(e\), a
contradiction. The first projection is therefore injective. The second
projection has nonzero image by the choice of \(q\), hence is surjective
by simplicity. Transport the second projection to the first image.

This is an algebraic form of the passage from a compact-type corner to an
ambient constituent in R. P. Langlands, *On the notion of an automorphic
representation* (1979), printed pp. 205–206, PDF pp. 200–201 of
Corvallis Part I (`langlands-1979-notion-automorphic-representation`).
The idempotent, corner action and subspace are supplied.
