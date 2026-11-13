# A split-centralizing transporter of special apartments over the maximal unramified extension

`UnramifiedFixedPointTransporterStatement` is the first of three geometric
inputs into which the fixed-locus statement
`UnramifiedTorusUnitFixedApartmentStatement` (Kaletha–Prasad Proposition
9.3.13) is split. The setting is the same as in that statement:

- \(F\) is a nonarchimedean local field, and \(K\) is its maximal unramified
  extension `inertiaFixedField F`, with the canonical integer valuation.
- \(G\) is a connected reductive group over \(F\).
- \(S\) is a maximal \(F\)-split torus of \(G\), and \(f : S \to T\) factors its
  inclusion through an \(F\)-torus \(T\). The extension \(T_K\) is a maximal
  \(K\)-split torus of \(G_K\).
- `D` is apartment data for \(T_K\) whose valuation class satisfies V 6 for
  the actual centralizer `C`, and `hD` says this class is Galois stable.

The remaining inputs are:

- an apartment point \(x_0\) fixed by the coefficient action of every
  \(\sigma \in \operatorname{Aut}(K/F)\);
- a point \(y\) of the reduced building `D.ReducedBuilding` that is fixed by
  the coefficient quotient action `galoisQuotientAction` of every \(\sigma\), and
  by every point of \(S_K(K)\) in its character-valuation kernel
  (`IsFixedByUnramifiedTorusUnits`).

The conclusion is an element \(h \in G(K)\) with four properties:

1. \(h\) commutes with the image of every point of \(S_K(K)\);
2. \(h\) fixes the image \([x_0]\) of \(x_0\) in the building;
3. for every \(\sigma\), the element \(h^{-1}\sigma(h)\) lies in the normalizer
   points of \(T_K\), where \(\sigma(h)\) is the coefficient conjugate
   `rationalConjugate`;
4. \(y = h \cdot [x_1]\) for some apartment point \(x_1\).

Put differently, \(hT_Kh^{-1}\) is a \(\operatorname{Aut}(K/F)\)-stable maximal
\(K\)-split torus containing \(S_K\), and its apartment
\(h \cdot A(T_K)\) contains both \([x_0]\) and \(y\).

## Provenance

This is a derived formulation. The mathematical source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. It
combines two of its results:

- Proposition 9.3.11(1), printed page 337 (PDF page 368). Two points of
  \(B(G_K)^{\Gamma}_S\) lie in the apartment of \(T_{1,K}\) for one special
  \(F\)-torus \(T_1 \supseteq S\). Here \([x_0]\) is such a point: the
  units of \(T_K\), and hence those of \(S_K\), fix the apartment.
- Proposition 9.3.12, printed pages 337–338 (PDF pages 368–369), applied over
  \(K\) in place of \(F\) with \(\Omega = \{x_0\}\) and the maximal \(K\)-split
  tori \(T_K\) and \(T_{1,K}\). It gives \(h \in G(K)^0_{x_0}\) commuting with
  \(S\) and carrying \(A(T_K)\) onto \(A(T_{1,K})\). Hence
  \(hT_Kh^{-1} = T_{1,K}\).

Since \(T_{1,K}\) is defined over \(F\),
\(\sigma(h)T_K\sigma(h)^{-1} = hT_Kh^{-1}\), which is item 3. Item 4 holds
because \(y \in A(T_{1,K}) = h \cdot A(T_K)\).

The authors' *Corrections and additions*, version of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
pages 39–40, must be used with both results:

- In the proof of 9.3.11 the references become 8.2.1(1),(5) and 9.3.5(1).
- Proposition 9.3.12 adds the hypothesis that \(\Omega\) is contained in an
  apartment of the building, and deletes the superscripts \(\Gamma\) in its
  conclusion. A single point \(x_0\) satisfies the added hypothesis.
- The new paragraphs before Proposition 9.3.13 apply 9.3.12 exactly in this
  way: over \(K\), with \(\Omega = \{x\}\), to obtain an element that commutes
  with \(S\), fixes \(x\) and transports one special apartment to the other.

In this formalization, \(S(K)_b\), the maximal bounded subgroup of \(S(K)\),
is the character-valuation kernel of \(S_K(K)\), as in
`UnramifiedTorusUnitFixedApartmentStatement`. "Commutes with \(S\)" means
commuting with all \(K\)-points of \(S\).

No proof is provided here; the Lean declaration is a proposition definition.
