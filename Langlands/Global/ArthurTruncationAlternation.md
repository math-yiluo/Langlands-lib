# Alternation of the chamber cutoffs

`alternatingCutoff_eq_zero` is the finite combinatorial step in Arthur's constant-term calculation. The allowed simple roots are divided into a free set and a neutral set. The payload depends on a subset only through its intersection with the neutral set. A cutoff is one when the remaining simple-weight evaluations are all strictly positive.

If any summand passes the cutoff, weights at roots outside the allowed set are positive. Their coefficients in the tested transported weight are nonpositive, and the neutral coefficients are zero. Strict positivity of the tested weight therefore forces a positive evaluation at a free root. Inserting or deleting that root preserves the cutoff and the payload and reverses the sign. The proof partitions the finite powerset into those pairs. If no subset passes the cutoff, every summand vanishes separately.

This is a finite-set form of the cancellation in Arthur's proof of Lemma 1.1 in *A trace formula for reductive groups II* (1980), pp. 89–91. On p. 91, Arthur applies Proposition 1.1 of *A trace formula for reductive groups I* (1978), p. 916.
