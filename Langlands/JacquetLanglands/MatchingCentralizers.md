# Centralizers of matching regular elements

Let \(g \in \mathrm{GL}_n(F)\) and \(g' \in D^\times\) correspond, where \(F\) has
characteristic zero and \(D\) is a finite-dimensional central division algebra
over \(F\). Their common characteristic polynomial \(p\) is irreducible.
`Corresponds.centralizerAlgebraEquiv` identifies their centralizer algebras over
\(F\) by identifying both with \(F[X]/(p)\), with \(X\) sent to \(g\) and \(g'\)
respectively. In particular the isomorphism sends \(g\) to \(g'\).

Evaluation at either element gives an embedding of \(F[X]/(p)\) with image the
singleton adjoin. On the matrix side that adjoin has the same dimension as the
regular centralizer. On the division side its dimension is the reduced degree.
If an element commutes with \(g'\), the two elements generate a commutative
finite-dimensional field. In characteristic zero this field has a primitive
element, whose minimal-polynomial degree is bounded by the reduced degree.
Thus the field equals the adjoin of \(g'\), establishing the centralizer
identity.

When \(F\) is nonarchimedean local and \(D\) carries its \(F\)-module topology,
`Corresponds.centralizerEquiv` identifies the topological groups of
centralizing units. The algebra maps and their inverses are continuous linear
maps of subspaces with the module topology. The units of each centralizer
algebra identify with the corresponding group centralizer using both the
element and its inverse in the definition of the units topology. The
isomorphism sends \(g\) to \(g'\) and sends each scalar unit over \(F\) to the
same scalar unit on the division side.

This is the centralizer identification used to transport associated Haar
measures in Badulescu, *Correspondance de Jacquet–Langlands pour les corps
locaux de caractéristique non nulle* (2002), §6, printed p. 746
(`badulescu-2002-jl-char-p`).
