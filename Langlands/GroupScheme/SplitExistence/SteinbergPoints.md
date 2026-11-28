# Normalized root coordinates and Steinberg words

For Chevalley data on a finite reduced root datum with base, this module
constructs root points \(x_j(t)\), Weyl words \(w_j(a)\) and torus words
\(h_j(a)\) in the represented group of \(k\)-points. The field \(k\) is
arbitrary, \(t\) ranges over \(k\), and \(a\) ranges over \(k^\times\).

`ChevalleyData.steinbergSign j` is an integral unit \(\epsilon_j\).
`ChevGroup.steinbergX j t` is the point `rootPt j` evaluated at
\(\epsilon_j t\). Both signs of a simple opposite pair are \(1\).
`steinbergRootCoordEquiv` identifies these coordinates with the rational
points of the represented root subgroup by scaling the existing coordinates
by the image of \(\epsilon_j\) in \(k^\times\). It uses the finite free
character lattice and the affine and locally finite type hypotheses of the
root subgroup representation.

For a positive root \(j\), choose a word of simple reflections carrying a
simple root \(i\) to \(j\), using the empty word if \(j\) is simple.
The Weyl point of the word is the product of its simple Weyl points.
At each step the Chevalley data give an integral sign for conjugating a
root coordinate. The product of those signs along the word determines the
coordinate of a transported root over every field. The same word sends
\(-i\) to \(-j\), so it determines both coordinate signs. Conjugating
`simpleRankOne i` by the word point gives `rootRankOne j`. Precomposing
with `sl2Swap` gives `rootRankOne` for the opposite root and exchanges
its upper and lower unipotent matrices.

Conjugation by a simple Weyl point transports the diagonal coroot point
because the reflected coroot pairs with a character as the original
coroot pairs with the reflected character. Composing the automorphisms
of the torus along the word gives the reflection of the transported root
for the standard Weyl matrix. The diagonal factor introduced by `sl2Swap`
centralizes the torus, and the root and its opposite define the same
reflection.

The definitions `steinbergW` and `steinbergH` are the literal products
\[
w_j(a)=x_j(a)x_{-j}(-a^{-1})x_j(a),\qquad
h_j(a)=w_j(a)w_j(-1).
\]
In \(\mathrm{SL}_2(k)\), the first word is the product of
\(\operatorname{diag}(a,a^{-1})\) and the standard Weyl matrix.
Computing its inverse and its product with an upper unipotent matrix,
then applying `rootRankOne j`, proves
\[
w_j(a)^{-1}=w_j(-a),\qquad
w_j(a)x_j(t)w_j(-a)=x_{-j}(-a^{-2}t).
\]
The product at \(a\) and \(-1\) is the diagonal matrix, so
`steinbergH_eq_corootPt` computes \(h_j(a)\) as the coroot point and
`steinbergH_eq_eval` identifies it with the actual coroot of `chevDatum k P`
evaluated at \(a\) and included into the group. The latter comparison uses
the finite free character lattice. The diagonal factor centralizes the
torus, hence `isNormalizingPoint_steinbergW` gives the normalizing action
of every \(w_j(a)\) through the reflection \(s_j\) on the torus as a group scheme.

The rank-one conventions are those of Robert Steinberg, *Lectures on Chevalley
Groups*, AMS 2016, Chapter 3, Lemma 19, pp. 22–23, and Chapter 6, relations
(A), (B′) and (C), p. 43. The literature ID is
`steinberg-2016-lectures-chevalley-groups` and the retained PDF has SHA-256
`e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
