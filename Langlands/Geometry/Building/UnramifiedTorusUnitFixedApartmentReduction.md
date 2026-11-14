# Reduction of the torus-unit fixed-apartment statement to three inputs

`UnramifiedTorusUnitFixedApartmentReductionStatement` says that three inputs
together imply exactly `UnramifiedTorusUnitFixedApartmentStatement` (the
\(K\)-level form of Kaletha–Prasad Proposition 9.3.13), at every universe
level. The three inputs are:

- `UnramifiedFixedPointTransporterStatement`: a transporter
  \(h \in G(K)\) that commutes with \(S\), fixes a fixed apartment point, and
  has normalizing cocycle.
- `UnramifiedTwistedFixedTranslationStatement`: twisted-fixed translations
  are split directions.
- `UnramifiedSplitTranslationFixerStatement`: an \(S\)-centralizing fixer of
  \([x]\) fixes \([v + x]\) for split directions \(v\).

`unramifiedTorusUnitFixedApartmentReduction` proves this implication. It
proves none of the three inputs, so it does not prove the fixed-apartment
statement unconditionally.

## The implemented proof

Fix the data of the target. Let \(y\) be a building point fixed by the
coefficient action and by the units of \(S_K(K)\).

1. **Injectivity.** The base change of \(G\) to \(K\) is connected reductive
   (`connectedReductiveFieldExtensionStatement`). The published theorem
   `KPApartmentData.apartmentMap_injective` therefore shows that the apartment
   map `D.apartmentMap` is injective.
2. **A fixed apartment point.** The published theorem
   `unramifiedGaloisFixedApartment` gives an apartment point \(x_0\) whose
   underlying function is fixed by every \(\sigma\). By
   `KPApartmentData.galoisAction_val` and `KPApartmentData.Apartment.ext`,
   \(x_0\) is fixed by the apartment Galois action.
3. **The transporter.** The first input, applied to \(x_0\) and \(y\), gives
   \(h\) and an apartment point \(x_1\) with \(y = h \cdot [x_1]\). The
   element \(h\) commutes with \(S_K(K)\), fixes \([x_0]\), and satisfies
   \(n_\sigma := h^{-1}\sigma(h) \in N(T_K)\).
4. **Twisted fixedness.** Let \(x\) be an apartment point with
   \(h \cdot [x]\) coefficient-fixed. Then \(n_\sigma \cdot \sigma(x) = x\)
   in the apartment:
   - semilinearity of the quotient action
     (`galoisQuotientAction_smul`, `galoisQuotientAction_apartmentMap`) gives
     \(\sigma(h) \cdot [\sigma(x)] = h \cdot [x]\);
   - multiplying by \(h^{-1}\) and using `D.apartmentMap_smul` gives
     \([n_\sigma \cdot \sigma(x)] = [x]\);
   - injectivity removes the brackets.

   This applies to \(x_0\), because \(h\) fixes \([x_0]\) and
   \(\sigma(x_0) = x_0\), giving \(n_\sigma \cdot x_0 = x_0\). It applies to
   \(x_1\), because \(h \cdot [x_1] = y\).
5. **The difference is twisted-fixed.** Write \(x_1 = (x_1 - x_0) + x_0\).
   Then `galoisAction_vadd` and `smul_vadd` rewrite
   \(n_\sigma \cdot \sigma(x_1)\) as
   \(n_\sigma \cdot \sigma(x_1 - x_0) + n_\sigma \cdot x_0\), using the
   translation actions `galoisTranslationAction` and `translationAction`.
   Since \(n_\sigma \cdot x_0 = x_0\), cancelling \(x_0\) shows that
   \(x_1 - x_0\) is fixed by every twisted map
   \(v \mapsto n_\sigma \cdot \sigma(v)\).
6. **Split directions.** The second input puts \(x_1 - x_0\) in
   `splitTranslationDirections`.
7. **Fixing \(y\).** The third input, with \(g = h\) and \(x = x_0\), shows
   that \(h\) fixes \([(x_1 - x_0) + x_0] = [x_1]\). Hence
   \(y = h \cdot [x_1] = [x_1]\).
8. **Conclusion.** For each \(\sigma\), coefficient-fixedness of \(y = [x_1]\)
   and `galoisQuotientAction_apartmentMap` give
   \([\sigma(x_1)] = [x_1]\). Injectivity yields \(\sigma(x_1) = x_1\), whose
   underlying functions agree. So \(x_1\) is the required fixed apartment
   point with image \(y\).

The proof raises `maxHeartbeats` to 8000000 and
`synthInstance.maxHeartbeats` to 400000. Elaborating the large base-change
types of this setting needs the extra budget.

## Provenance

This is an internal derived reduction. Its route follows Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.3.13 and its
proof, printed page 338 (PDF page 369). The book is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The route
also uses the authors' corrected independence paragraph before 9.3.13, from
the *Corrections and additions*, version of 1 November 2024, PDF pages 39–40,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

Each of the three inputs carries its own citation. The reduction uses no
covering statement, no full building-descent statement, and no consumer of
the target.
