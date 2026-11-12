# Finite chamber galleries along rational segments

This is internal linear algebra for Task 5515. `SparseInterval s a b`
means that the open interval from `a` to `b` contains at most one member
of a finite set of rational breakpoints.

`reflTransGen_of_sparse_intervals` proves that a relation holding on every
such sparse interval, for regular endpoints inside the specified range,
connects the full endpoints by a finite chain. The proof inducts on the
finite breakpoint set. If there are at most one, the whole interval is a
single step. Otherwise it chooses a cut strictly between the two least
breakpoints. The first subinterval has just the least breakpoint; the
remaining breakpoints all lie strictly to the right of the cut. Applying
the induction hypothesis to that remainder finishes the chain. Thus no
chain vertex belongs to the breakpoint set.

The construction is derived elementary content. It asserts no group-scheme
or representation-theoretic conclusion.
