# The unit-fixed coefficient-fixed locus of a special apartment

`UnramifiedTorusUnitFixedApartmentStatement` isolates the fixed-locus input
to the unramified building covering argument. Its field, connected
reductive group, maximal \(F\)-split torus \(S\), containing \(F\)-torus
\(T\) maximal split over \(K\), compatible root-valuation class, actual
centralizer, V 6, and Galois-stability hypotheses are those of
`UnramifiedGaloisFixedBuildingPointStatement`.

If a building point is fixed by the coefficient action of
\(\operatorname{Aut}(K/F)\) and by the character-valuation kernel of
\(S_K(K)\), then it is the apartment image of an
\(\operatorname{Aut}(K/F)\)-fixed apartment point. The units here are the
units over \(K\), evaluated through the base change of the inclusion of
\(S\). Fixity of the apartment preimage is part of the conclusion, so this
interface does not assume a separate apartment-injectivity theorem.

The mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 9.3.13, printed page 338 (PDF page 369),
which identifies this simultaneous fixed locus with the fixed apartment
of \(T\). The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The use of the intrinsic character-valuation kernel is a derived
formulation of the split torus unit subgroup.

Read the authors' *Corrections and additions*, version of 1 November 2024,
PDF pages 39–41, registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The correction before Proposition 9.3.13 supplies the missing independence
of the \(V(S')\)-action from the chosen special apartment and deletes the
original proof's final paragraph. A proof must use the corrected argument.
For Proposition 9.3.11 the corrected references are 8.2.1(1),(5) and
9.3.5(1). No proof of this geometric prerequisite is provided here; the
Lean declaration is a proposition definition.
