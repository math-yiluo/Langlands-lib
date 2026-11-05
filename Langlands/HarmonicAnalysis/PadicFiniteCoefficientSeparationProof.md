# Common prime-power scaling detects finite coefficient families

Author: Worker 84. The theorem
`Langlands.HarmonicAnalysis.padicFiniteCoefficientSeparation.{u}`
proves `Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement`.

Write \(n\) for the existing additive conductor and
\(e=\operatorname{ord}_F(p)\), which is a positive integer. The proof
chooses the natural-number bound
\[
 B=\max\bigl(\{\,\max(0,\operatorname{ord}_F(a)+n-m+1):a\in s\,\}
                 \cup\{0\}\bigr).
\]
In Lean this is `Finset.sup` of `Int.toNat`. For every \(N\geq B\),
each coefficient satisfies
\(\operatorname{ord}_F(a)+n-m+1\leq N\leq Ne\).

Suppose \(a\neq0\) and the scaled character is trivial on the prescribed
lattice. The actual prime element and its integer powers are nonzero.
The published lattice-annihilator implication puts \(p^{-N}a\) in
the lattice of level \(n-m\). The identity
\(v(y)=\exp(-\operatorname{ord}_F(y))\) for nonzero \(y\), valuation
multiplicativity, and the integer-power order law then give
\[
 Ne-\operatorname{ord}_F(a)\leq n-m.
\]
This contradicts the preceding bound. For \(a=0\), the character value
is one for every test element by additivity.

The proof imports the unchanged target and the existing additive
self-duality module for its lattice-annihilator implication. It
constructs no new valuation, topology, lattice, character or conductor.
The argument handles an empty coefficient set, every integer lattice
level, every supplied topology and every prime, including two.
It is an internal consequence of the existing declarations named in
the target Markdown. The remaining multiplicative auxiliary-character
obligations listed there are outside this theorem.
