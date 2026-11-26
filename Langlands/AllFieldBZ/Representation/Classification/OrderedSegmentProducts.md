# Ordered inductions attached to a Zelevinsky segment

Let \(F\) be a nonarchimedean local field, let \(\nu=|\det|_F\) use the
residue-normalized absolute value, and let \(\Delta=[\rho,\nu^{m-1}\rho]\) start
with a supercuspidal class of \(\operatorname{GL}_r(F)\). For an actual smooth
supercuspidal representative \(A\) of \(\rho\), `segmentFactor` constructs
\(\nu^i A\) and identifies its supercuspidal class with `Δ.member i`.

`segmentInduced` and `segmentInducedDown` use `cuspidalProductInduced` on
\(\operatorname{GL}_{mr}(F)\). They are the normalized smooth inductions from
the standard upper parabolic with \(m\) blocks of size \(r\), using respectively
the factors \((A,\nu A,\ldots,\nu^{m-1}A)\) and
\((\nu^{m-1}A,\ldots,\nu A,A)\). The reversal uses `Fin.rev`. For each product,
the isomorphism declaration applies `cuspidalProductInducedIsoOfRepresented`
to the corresponding factors. The finite-length lemmas apply
`Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength` using
irreducibility of the actual supercuspidal twists.

`IsSegmentSocle` describes an actual irreducible embedding into the
increasing-order product, with equality of the images of all irreducible
embeddings. `IsSegmentHead` describes an actual irreducible quotient of the
same product, with equality of the kernels of all irreducible quotient maps.
These predicates give the increasing-order descriptions of
\(\langle\Delta\rangle\) and the special representation
\(\langle\Delta\rangle^t\), respectively. They describe a supplied smooth
representation and quantify over representatives of the beginning of the segment.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)* (1980), §§3.1 and 9.1, printed
pp. 180–181 and 197, literature ID `zelevinsky-1980-induced-ii`. These sections
give the two orders of the segment induction and describe the ordinary segment
representation and its special counterpart.
