# Underlying graphs of finite Cartan matrices

This private intermediate development associates an unoriented simple graph
`diagram M` to a matrix, joining distinct indices when both ordered entries
are nonzero. For a finite Cartan matrix this is equivalent to the single
ordered entry being negative, because zero entries are symmetric.

If a graph `H` is contained in this diagram, entrywise comparison with twice
the identity minus the adjacency matrix of `H` bounds the image of the
constant vector one by `2 - degree H i`. The positive-coordinate obstruction
therefore gives a vertex of `H` of degree at most one.

An injective copy of a cycle would give a finite Cartan principal submatrix
with a contained graph of constant degree two. This contradicts the preceding
bound, and proves that the diagram is acyclic. The construction and arguments
are internal consequences of Mathlib's finite Cartan predicate; they do not
invoke any classification or group-theoretic result.

Indecomposability implies connectedness by a direct block decomposition. A
nontrivial predicate separating two vertices, with every entry from its
complement into it zero, gives a forbidden block triangular reindexing after
numbering the two finite subtypes. Apply this to reachability from a fixed
vertex to prove connectedness. Together with acyclicity this makes the diagram
a tree.

The row edge-product bound gives degree at most three: each adjacent vertex
contributes at least one, while all other off-diagonal edge products are
nonnegative.
