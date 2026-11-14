# Centralizers of split units fix split translates in the building over the maximal unramified extension

`UnramifiedSplitTranslationFixerStatement` is the third of three geometric
inputs into which `UnramifiedTorusUnitFixedApartmentStatement` (Kaletha–Prasad
Proposition 9.3.13) is split.

## Setting

- \(F\) is a nonarchimedean local field, and \(K\) is its maximal unramified
  extension `inertiaFixedField F`, with the canonical integer valuation.
- \(G\) is a connected reductive group over \(F\).
- \(S\) is a maximal \(F\)-split torus, and \(f : S \to T\) factors its
  inclusion through an \(F\)-torus \(T\) whose extension \(T_K\) is maximal
  \(K\)-split in \(G_K\).
- `D` is apartment data for \(T_K\) whose valuation class satisfies V 6 for
  the actual centralizer `C`.

No Galois-stability hypothesis is needed.

## Statement

Let \(g \in G(K)\) commute with every point of \(S_K(K)\). Suppose \(g\) fixes
the image \([x]\) in `D.ReducedBuilding` of an apartment point \(x\). Then
\(g\) fixes \([v + x]\) for every \(v\) in `splitTranslationDirections`, the
image of \(V(S_K)\) among the apartment translations (defined in
`UnramifiedTwistedFixedTranslationStatement`).

## Mathematical content and provenance

This is a derived formulation of the argument added before Proposition 9.3.13
by the authors' *Corrections and additions to Bruhat–Tits Theory: A New
Approach*, version of 1 November 2024, PDF pages 39–40. That document is
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

There, \(g\) commutes with \(S\) and fixes \(x\), and \(f\) is multiplication
by \(g\) from a special apartment \(A_1\) to \(A_2\). The set of points of
\(A_1\) fixed by \(f\) is closed and convex. It contains every \(s \cdot x\)
for \(s \in S'\), because \(g(s \cdot x) = s \cdot (g \cdot x) = s \cdot x\).
Since the closed convex hull of these points in \(A_1\) is
\(V(S') + x\), \(g\) fixes \(v + x\) for every \(v \in V(S')\).

Here the same argument is applied over \(K\) inside the single apartment of
\(T_K\). The \(K\)-points of \(S_K\) act on \([x]\) by translations in the image
of \(V(S_K)\), and these translations form a lattice spanning that image.
Convexity of the fixed set of \(g\) then gives all of
`splitTranslationDirections` \(+\, x\).

The paragraph corrects the original book, Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 9.3.13, printed page 338 (PDF page
369), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The
corrections delete the last paragraph of the book's proof of 9.3.13 and
replace it with this independence argument.

No proof is provided here; the Lean declaration is a proposition definition.
