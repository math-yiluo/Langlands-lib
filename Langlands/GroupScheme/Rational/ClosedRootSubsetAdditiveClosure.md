# Additive generation of closed root subsets

This module contains two internal lemmas for the proof of Borel–Tits 3.22 c).
They are derived combinatorial content, rather than new statements attributed
to the literature.

`rootPairing_mem_of_mem_addSubmonoidClosure` proves saturation of a closed
subset of a finite crystallographic root pairing among roots of its generated
additive monoid. It expresses a generated element as a multiset sum and uses
strong induction on that multiset. Pairing the root sum with its own coroot
gives two, so a summand has positive pairing. If that summand is the entire
sum, it already belongs to the original subset. Otherwise Mathlib's
positive-pairing root-difference lemma shows that the sum of the remaining
multiset is another root. Induction and closedness under root sums finish.
No reducedness assumption is used, and the argument also covers the additive
monoid's empty sum because zero is not a root.

`IsClosedRootSubset.mem_of_mem_addSubmonoidClosure` specializes this result to
the actual, possibly nonreduced `relativeRoots i` of a maximal split torus in
a connected reductive group over a field. The published `relativeRootSystem`
theorem provides the finite crystallographic root pairing on the rational
root span. Closure induction lifts the additive monoid of characters to the
additive monoid of rational roots in that span. The equality of the two root
sets transports closedness, and injectivity of character rationalization for
a split torus transports the result back to the original character lattice.
