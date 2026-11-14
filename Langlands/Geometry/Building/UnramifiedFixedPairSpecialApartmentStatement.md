# Two fixed building points in one centralizing translate of a special apartment

`Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentStatement` is a
proposition definition, in arbitrary universe `u` and for both characteristics. It
expresses Kaletha–Prasad Proposition 9.3.11(1), for a maximal \(F\)-split torus
\(S\), as a statement about one translate of the supplied apartment.

## Setting

The hypotheses are exactly those of
`UnramifiedFixedPointTransporterStatement`, up to and including `hD`:

- \(F\) is a nonarchimedean local field, and \(K\) is its maximal unramified
  extension `inertiaFixedField F`, with the canonical integer valuation
  `IntegerValuation.order (MaximalUnramified.valuation F)`.
- \(G\) is a connected reductive group over \(F\).
- `iS : S.toGrp ⟶ G` is a maximal \(F\)-split torus, and `f : S ⟶ T` factors it
  through `iT : T.toGrp ⟶ G` (`groupHom f ≫ iT = iS`). The base change
  \(i_{T,K}\) is a maximal \(K\)-split torus of \(G_K\) (`hiT`).
- `D : KPApartmentData` is apartment data for \(i_{T,K}\) whose valuation class
  satisfies full V 6 (`IntegerValuation.IsOmegaCompatible`) for the actual
  centralizer datum `C`. The hypothesis `hD : KPApartmentData.GaloisStable F K iT D`
  supplies the coefficient action `KPApartmentData.galoisQuotientAction` of every
  \(\sigma \in \operatorname{Aut}(K/F)\) on `D.ReducedBuilding`.

The proposition then takes two points \(y_1, y_2\) of `D.ReducedBuilding`. Each
\(y_i\) satisfies:

1. \(\sigma(y_i) = y_i\) for every \(\sigma \in \operatorname{Aut}(K/F)\), using
   `galoisQuotientAction`;
2. `IsFixedByUnramifiedTorusUnits F iS yᵢ`: \(y_i\) is fixed by the image in
   \(G(K)\) of every point of \(S_K(K)\) in the character-valuation kernel for the
   canonical valuation. For the split torus \(S_K\) this kernel is the maximal
   bounded subgroup \(S(K)_b\).

## Conclusion

There is \(g \in G_K(K)\) (a point of `rationalPoints (baseChanged F K G)`) such
that:

1. \(g\) lies in `centralizerPoints` of \(i_{S,K}\). This is the published
   centralizer evaluated at \(\operatorname{Spec} K\); by
   `commute_of_mem_centralizerPoints`, \(g\) commutes with every point of
   \(S_K(K)\).
2. For every \(\sigma \in \operatorname{Aut}(K/F)\), the element
   \(g^{-1}\sigma(g)\) lies in `normalizerPoints` of \(i_{T,K}\), the published
   normalizer of the embedded torus. Here \(\sigma(g)\) is
   `rationalConjugate F K G σ g`.
3. \(g \cdot\) `D.apartmentMap` \(x_1 = y_1\) for some \(x_1\) : `D.Apartment`.
4. \(g \cdot\) `D.apartmentMap` \(x_2 = y_2\) for some \(x_2\) : `D.Apartment`.

So one translate \(g \cdot A(T_K)\) of the supplied apartment contains both points.
Its representative \(g\) centralizes \(S_K\), and its Galois differences normalize
\(T_K\). Then \(gT_Kg^{-1}\) is an \(\operatorname{Aut}(K/F)\)-stable maximal
\(K\)-split torus containing \(S_K\). The statement does not require \(g\) to fix
either point.

## Provenance

This is a derived formulation, not a transcription. The source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- The paragraph before Proposition 9.3.11, printed page 337 (PDF page 368),
  defines \(B(G_K)_S\) as the set of points fixed by \(S(K)_b\), for a \(k\)-split
  torus \(S\). \(B(G_K)^{\Gamma}_S\) is its subset of \(\Gamma\)-fixed points.
  Hypotheses 1 and 2 above say exactly that \(y_i \in B(G_K)^{\Gamma}_S\).
- Proposition 9.3.11(1), on the same page: for \(x, y \in B(G_K)^{\Gamma}_S\)
  there is a special \(k\)-torus \(T_1 \supseteq S\) such that both points lie in
  the apartment of \(B(G_K)\) corresponding to \(T_{1,K}\). The present
  statement applies it only when \(S\) is a maximal \(F\)-split torus.

The authors' *Corrections and additions*, version of 1 November 2024, are
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. On PDF page 39
they change the references in the proof of 9.3.11 to Proposition 8.2.1(1),(5) and
Proposition 9.3.5(1); the statement of 9.3.11 is unchanged. The proof takes the
schematic closure of \(S\) in the Bruhat–Tits group scheme of the geodesic
\([x, y]\) (Proposition B.2.4) and a special \(k\)-apartment containing \([x, y]\)
(Proposition 9.3.8). It then conjugates split tori in the special fibre, lifts the
result (8.2.1), and concludes with 9.3.5. The new paragraphs before
Proposition 9.3.13 (PDF pages 39–40) use 9.3.11 for points of
\(B(G_K)^{\Gamma}_S\) in this way.

Two translations turn the source conclusion into the present form.

- **The building.** The source building \(B(G_K)\) is compared with
  `D.ReducedBuilding`, built from the supplied full V 6 valuation class. The
  comparison rests on uniqueness of compatible valuation classes, Proposition
  6.2.6, printed page 216 (PDF page 247). The apartment of a torus
  \(gT_Kg^{-1}\) is the translate \(g \cdot A(T_K)\).
- **The torus \(T_{1,K}\) as a translate of \(T_K\).** \(T_{1,K}\) and \(T_K\)
  are maximal \(K\)-split tori of \(G_K\) containing \(S_K\). So they are
  conjugate by a point of \(Z_{G_K}(S_K)(K)\). The published
  `Langlands.GroupScheme.exists_centralizing_conj_of_isMaximalSplitTorus`, in
  `Langlands.GroupScheme.Reductive.TitsIndexCentralizerConjugacy`, gives such a
  conjugator \(g\) for two maximal split tori through which the same split-torus
  homomorphism factors. Both \(T_1\) and \(T\) are defined over \(F\). So
  \(\sigma(g)\) also conjugates \(T_K\) to \(T_{1,K}\), and the published
  `Langlands.GroupScheme.inv_mul_mem_normalizerPoints_of_transporters`, in
  `Langlands.GroupScheme.Rational.TorusTransporterOrbit`, gives
  \(g^{-1}\sigma(g) \in N_{G_K}(T_K)(K)\).

These translations are part of the proof obligation of the statement. The
statement does not assert that the special torus \(T_1\) or any integral model
exists as a Lean object; it keeps only the translated-apartment consequence.
Proposition 9.3.12 is not used here. The extra requirement that the conjugator
fix a chosen point belongs to `UnramifiedFixedPointTransporterStatement`. The
supporting module `Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction`
derives that statement from the present one.

This file defines the proposition only. It contains no proof of the
common-apartment assertion.
