# Norm, trace and epsilon bases at split finite places

At a finite place with an upper completion of degree one, the scalar map is a
section of the local norm on units. Thus the finite component of a global
norm-trivial Hecke character is trivial. The standard upper additive component
pulled back by the completed scalar isomorphism is the standard lower component,
since the relative trace of the scalar inclusion is the identity. The two
residue cardinalities coincide by the degree formula and the ideal norm formula.

`SplitCompletionEpsilonBaseStatement` compares the actual positive finite epsilon
bases at a place whose globalization tensor is cyclic-shift split. It assumes
that the lower family is indexed by a finite type of cardinality `[L : K]` and
that each lower and upper factor has the same supplied exponent. Every upper
completion has degree one. The number of upper places is therefore `[L : K]`, by
the ramification-inertia sum formula. Both finite bases are the same power of
the common residue cardinality.

These are internal arithmetic and additive reductions for the split finite
place comparison in Arthur–Clozel, Chapter 1, Proposition 6.9(ii) and Lemma 6.13,
printed p. 70 (PDF p. 84).
