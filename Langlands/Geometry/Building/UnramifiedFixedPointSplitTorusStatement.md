# A maximal split torus whose units fix a prescribed fixed point

`UnramifiedFixedPointSplitTorusStatement` is a geometric prerequisite of the
unramified building covering theorem. Let \(F\) be a nonarchimedean local
field, \(K\) its maximal unramified extension, and \(G\) a connected reductive
group over \(F\). The supplied \(F\)-torus \(T\) becomes maximal split over
\(K\). Its supplied class of root valuations satisfies V 6 for the actual
centralizer and the canonical integer valuation, and is Galois stable.

Every point of this reduced building fixed by the coefficient action of all
\(F\)-automorphisms of \(K\) admits a maximal \(F\)-split torus \(S'\) such
that every point of \(S'(K)\) in its character-valuation kernel fixes the
given building point. The units are taken over \(K\). The statement does
not identify the point with a point of the originally supplied apartment.

This is a derived formulation of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 9.3.8, printed pages 335–336 (PDF pages
366–367), together with the unit fixation of an apartment. The special
apartment containing the prescribed point supplies \(S'\), and the units of
its extended split torus have zero translation. The book's Proposition
9.3.8 asserts common special-apartment containment for two fixed points;
this statement retains only the consequence needed for one point.
The book is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The authors' *Corrections and additions*, version of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
must accompany the book; its PDF pages 39–41 correct later comparisons in
this section. No proof of this geometric prerequisite is provided here.
The Lean declaration is a proposition definition.
