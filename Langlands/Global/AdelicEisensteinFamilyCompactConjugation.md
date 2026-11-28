# The family comparison under archimedean conjugation of the Iwasawa compact

Module `Langlands.Global.AdelicEisensteinFamilyCompactConjugation` proves that
`FamilyRegularComparison` (module `Langlands.Global.AdelicEisensteinFamilyRegularComparison`)
passes from a subgroup `K` of `G(𝔸)` to its conjugate `t⁻¹ K t` by an archimedean point
`t = ofInfinite F G s`.

## Statements

- `comap_ofInfinite_map_conj K a`: for an archimedean point `a`, conjugating
  `K' = (ofInfinite a)⁻¹ K (ofInfinite a)` back by `a` on the archimedean side recovers the
  archimedean part of `K`:
  `(K'.comap (ofInfinite F G)).map (conj a) = K.comap (ofInfinite F G)`. The proof is a direct
  computation with `ofInfinite` a group homomorphism.
- `FamilyRegularComparison.of_conjugateCompact`: let `K` have Iwasawa coverage for `P` and `Q`,
  let `s` be an archimedean point, `t = ofInfinite F G s`, and suppose `K' = t⁻¹ K t` has
  Iwasawa coverage for `P` and `Q` too. Then the predicate for `K` implies the predicate for
  `K'`, with the same group data and universes.

## Proof of the main theorem

Fix the data `φ, b, EP, ψ, coeff` for `K'`. `eisensteinConjugateCompactTransport` (module
`Langlands.Global.AdelicEisensteinConjugateCompactProof`) gives, for every function `φ`, every
`λ` and every `g`, the identities

- `E_{K'}(φ, λ)(g t) = H_{K'}(t)^λ · E_K(φ(· t), λ)(g)`,
- `E_{Q,K'}(φ, wλ)(g t) = H_{K'}(t)^{wλ} · E_{Q,K}(φ(· t), wλ)(g)`, and
- `M_{K'}(w, λ)φ (g t) = H_{K'}(t)^{-wλ} H_{K'}(t)^λ · M_K(w, λ)(φ(· t))(g)`,

where `H_{K'}(t)^λ` is the height factor `IsIwasawaCompact.heightPower` at `t`. These factors
are exponentials of linear forms in `λ`: `ℓP = -⟨·, H_P(t)⟩` and `ℓQ = ⟨w·, H_Q(t)⟩`
(`complexParameterPairingAt`). Here `H_P(t)` and `H_Q(t)` are the heights of `t` for `P` and
for `Q` with respect to `K'` (`IsIwasawaCompact.height` for `hKP'` and `hKQ'`), and
`w· = weylParameter l c π'`.

The data for `K` are the right translates `φ(· t)`, `ψ(· t)`, which are automorphic for the
archimedean part of `K` by `IsAutomorphicFunctionOn.infiniteRightTranslate` and
`comap_ofInfinite_map_conj`; the function `EP'(λ, g) = EP(λ, g t) · exp ℓP(λ)`; the same `b`;
and the coefficients `coeff i λ · exp ℓQ(λ) · exp ℓP(λ)`. Meromorphy is kept by
`IsMeromorphicInCoordinatesOn.mul_exp`. The series identity and the intertwining identity for
`K` follow from those for `K'` evaluated at `g t` and the three identities above, since the
height factors cancel against the exponentials. The predicate for `K` gives a patch on which
`EP'` is the sum of the `Q`-series for `K`. Evaluating at `g t⁻¹` and applying the `Q`-series
identity converts this back into the conclusion for `K'`.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, fix one maximal compact subgroup.
Archimedean conjugation moves a maximal compact subgroup in good position to one whose
archimedean component equals that of a given maximal compact subgroup.
