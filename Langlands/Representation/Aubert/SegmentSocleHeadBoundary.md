# Algebraic and supercuspidal boundary cases of segment duality

Author: Worker 165.

These are derived helper results for the segment socle–head task. They do
not assert the general segment exchange or the existence of any constituent.
They keep independent field and carrier universes and use the existing exact
finite-length Grothendieck group, including its nonsplit exact relations.

`SupercuspidalEigenvalueStatement` records the positive-rank supercuspidal
eigenvalue assertion and `supercuspidalEigenvalue` proves it uniformly.
Finite length is an explicit input; irreducibility is not required here.

`alternatingOperator_signed_reverse` applies the published involutivity
theorem to a supplied forward signed identity. Integer linearity and the
identity `((-1)^k)^2 = 1` recover the reverse signed identity.

`normalizedJacquetK0_supercuspidal` uses the published comparison between
supercuspidality and standard proper Jacquet vanishing. The actual normalized
Jacquet object has the same zero carrier as the unnormalized quotient.
The published class formula and zero-object class lemma then show that its
exact Grothendieck class vanishes.

`alternatingOperator_supercuspidal` expands the defining finite sum of
actual induction–Jacquet maps. Every proper standard Jacquet term vanishes
by the preceding lemma. A full block parabolic has at most one block, and
the cut-set parametrization identifies it with the empty-cut shape.
In positive rank that shape has one block. The published actual one-block
induction–Jacquet equivalence makes its map the identity. Its coefficient
is precisely the unadjusted sign `(-1)^(n-1)`.

The imported involutivity proof is an identity on all virtual classes; it
does not assert effectivity or irreducible preservation. The other imported
inputs are the actual one-block equivalence, block-shape combinatorics,
the standard-Jacquet comparison, and the zero-object class lemma. No
classification theorem or polynomial-ring description is used.
