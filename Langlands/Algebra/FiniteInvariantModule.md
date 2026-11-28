# A bound on module generators for nested rings of invariants

Let \(A\) be a nontrivial commutative algebra over a characteristic-zero field
\(k\). Let \(W\) be a finite group acting on \(A\) by \(k\)-algebra
automorphisms and let \(H\le W\). `InvariantModuleGeneratorBoundStatement`
uses the inclusion \(A^W\hookrightarrow A^H\) for the module structure.
If \(A\) has at most \(m\) algebra generators over \(k\) and \(|W|\le d\),
then \(A^H\) has a spanning family over \(A^W\) indexed by `Fin (d ^ m)`.

In `exists_spanningFamily_fixedPoints`, each generator \(a\) satisfies the
monic polynomial \(\prod_{w\in W}(X-w\cdot a)\) over \(A^W\). Its degree
is \(|W|\). The proof uses Mathlib's orbit polynomial and lifts its coefficients
to \(A^W\). Taking the remainder on division by this polynomial expresses each
element of \(A^W[a]\) in terms of the powers \(a^i\) with \(i<d\). Adjoining
the generators one at a time multiplies the spanning families, giving at most
\(d^m\) monomials for \(A\) over \(A^W\). The proof includes these monomials
in a family indexed by `Fin (d ^ m)` and fills unused indices with zero.

The sum of the \(H\)-translates of an element of \(A\) lies in \(A^H\), since
left multiplication by each \(h\in H\) permutes the summands. This trace
map is \(A^W\)-linear. It sends \(|H|^{-1}b\) to \(b\) for every \(b\in A^H\).
Applying the map to the spanning family for \(A\) gives the asserted family
for \(A^H\).

The bound isolates the invariant-ring calculation behind the finiteness
of the component maps used in Renard, *Représentations des groupes
réductifs p-adiques* (9 July 2026), VI.10.5, printed p. 213 (PDF p. 219).
