# Positive split components and parameters for nested adelic parabolics

This module supplies the group-theoretic transport behind a convention in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §8.1, p. 222. For \(Q\subseteq P\), \(a\in A_P\) and \(\lambda\in\mathfrak a_{Q,\mathbb C}^*\), the difference operator \(\Delta^{P,\lambda}_a\varphi=a\cdot\varphi-a^{\lambda}\varphi\) is defined because \(A_P\subseteq A_Q\), and its value depends only on the projection of \(\lambda\) to \(\mathfrak a_{P,\mathbb C}^*\). The module works with the actual members of a `StandardParabolicFamily` (the parabolic \(P\), its Levi \(M_P\) and its specified split component \(A_P\) with their closed inclusions). It constructs the needed scheme maps rather than assuming them.

## Inclusions for \(Q\le P\)

- `nestedParabolicHom hQP : 𝓕.P Q ⟶ 𝓕.P P` factors the closed inclusion of \(Q\) through the closed inclusion of \(P\). It uses the represented-subgroup factorization and the family's order comparison `le_iff_range_le`. `nestedParabolicHom_comp` gives the composite.
- `nestedLeviHom hQP : 𝓕.M Q ⟶ 𝓕.M P` factors the Levi of \(Q\) through the Levi of \(P\). The containment of the actual images is the Levi part of the published standard-parabolic order theorem `standardParabolicOrder`, after rewriting each Levi as its standard Levi by the family's compatibility. `nestedLeviHom_comp` gives the composite.
- `nestedSplitComponentHom hQP : 𝓕.A P ⟶ 𝓕.A Q` is the published `intermediateSplitComponentFactor` of the compatible root presentation of \(Q\). It applies to the closed intermediate group \(M_P\), which contains \(M_Q\) through `nestedLeviHom`, and to the split component of \(P\), which is central in \(M_P\). Its specification, `nestedSplitComponentHom_comp`, says that \(A_P\to A_Q\to M_Q\to M_P\) is the given inclusion \(A_P\to M_P\). The construction uses a choice. Uniqueness is not asserted.
- `nestedSplitComponentHom_parabolic_comp` proves that \(A_P\to A_Q\to M_Q\to Q\to P\) equals \(A_P\to M_P\to P\). It composes both sides with the monomorphism \(P\to G\) and cancels.

## Positive points and parameter values

`positiveSplitComponent J` is the image in \(J(\mathbb A_F)\) of the positive real points \(A_J(\mathbb A_F)^+\) of the split component (the intrinsic subgroup of `PositiveRealTorus`).

- `exists_positiveSplitComponent_lift` maps a positive point \(x\) of \(A_P\) to \(A_Q\) by `nestedSplitComponentHom`. The image is positive by the published functoriality `PositiveRealTorus.map_intrinsicSubgroup_le`, and its image in \(Q(\mathbb A_F)\) is a positive point \(b\) of \(Q\). By the previous identity, \(b\) maps to the given point of \(P(\mathbb A_F)\).
- `AdelicGroupPoints.parameterPower_parameterRestrict` is the general functoriality \(x^{j^*\lambda}=j(x)^{\lambda}\) for a map \(j:H'\to H\), an actual adelic point \(x\) of \(H'\) and a complex character parameter \(\lambda\) of \(H\). It combines the published pairing compatibility `complexParameterPairing_parameterRestrict` with `characterLog_map`.
- `exists_positiveSplitComponent_lift_with_values` proves that for each positive point \(a\) of \(P\) there is a positive point \(b\) of \(Q\) with the same image in \(G(\mathbb A_F)\), and with \(b^{\mathrm{res}\,\lambda}=a^{\lambda}\) for every parameter \(\lambda\) of \(P\), where \(\mathrm{res}\) is restriction along `nestedParabolicHom`.

Thus the raw left shift by \(a\) on functions on \(G(\mathbb A_F)\) equals the raw left shift by the positive point \(b\) of \(A_Q\). In the products of differences in the proof of BL Lemma 8.1, a shift from \(A_P\) may therefore be paired with exponents for \(Q\). The value at \(b\) of a restricted parameter of \(P\) is the value at \(a\) of that parameter. The module proves no statement about cuspidal tests, constant terms or the vanishing criterion (8.1).
