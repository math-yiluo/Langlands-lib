# Conjugacy respecting a common split-torus factorization

This internal supporting lemma is derived from the published split-torus
centralizer and smooth connected affine conjugacy results. It is intended for
the independence argument in maps on algebraic fundamental groups.

Let \(G\) be a smooth connected affine group over any field, let \(A\) be a split
commutative torus, and let \(i:T\to G\) and \(i':T'\to G\) be maximal split tori.
For arbitrary homomorphisms \(q:A\to T\) and \(q':A\to T'\) with
\(qi=q'i'\), the theorem constructs a rational point \(g\) and an isomorphism
\(e:T\simeq T'\) such that \(i\operatorname{Int}(g)=ei'\), \(qe=q'\), and
\(\operatorname{Int}(g)\) fixes the common homomorphism into \(G\).
The homomorphisms from \(A\) need not be closed immersions.
`splitTorusFactorizationConjugacy` selects this rational point and torus
isomorphism, bundled with all three equalities.

The implemented proof chooses a cocharacter of \(A\) whose dynamic centralizer
equals the centralizer of its whole image. Both maximal split tori lift to this
represented closed centralizer and remain maximal split there. Dynamic
smoothness and connectedness allow the published maximal split torus conjugacy
theorem to be applied inside this centralizer. Mapping its conjugating point
into \(G\) supplies the ambient conjugacy and the assertion that the common
image is fixed. Cancelling the closed immersion \(i'\) then gives \(qe=q'\).

The lemma uses published results by Lean name and has no additional external
source claim. It does not assert independence of quotient maps, Galois
equivariance, or the complete induced-map proposition.
