# The actual translated Levi and its transported quotient

Let `χG` be the cocharacter defining the standard Levi `M` of the
original parabolic, let `n` be a normalizer point with
`n · M ⊂ M'`, and let `χ` be `χG` followed by conjugation by `n`.
This module identifies the Levi `levi χ` of the translated parabolic
`n · P` with `M`. It also identifies the representation of `levi χ`
induced from `π` with the inducing representation of the lower family on
the common Levi in `M'`.

## Contents

- `weightedCLeviEquiv` is the topological group isomorphism
  `levi χ ≃ M`: inverse conjugation by `n` followed by
  `standardLeviDynamicHomeomorph`.
- `weightedCParameterIso` is the isomorphism of the reductive parameter
  schemes, the inverse of `parameterConjugationIso` composed with
  `standardLeviParameterIso`. By `weightedCParameterIso_hom_comp`, its
  composite with the standard Levi inclusion is the centralizer inclusion
  of `χ` followed by inverse inner conjugation by `n`.
  `weightedCParameterIso_points` shows that on rational points it is
  `weightedCLeviEquiv`.
- `weightedCParameterIso_lower` states that `auxiliaryInnerParameterIso`
  followed by `weightedCParameterIso` is `lowerParameterIso`.
- `weightedC_restrict_ambientDensity` and
  `weightedC_restrict_lowerDensity` show that the two restrictions of the
  lifted parameter of `z` are the arguments of the ambient and lower
  Plancherel densities: the character of the standard Levi, and its
  conjugate `x ↦ z(n⁻¹ x n)` on the lower Levi
  (`lowerUnramifiedCharacterConjugation`).
- `weightedCTranslatedCoefficientEquiv` is the identity of the carrier of
  `π`. It intertwines the restriction of the conjugate representation
  `conjugateRepresentation χG n (π ∘ eG)` to the common Levi with the
  lower inducing representation `lowerRepresentation`.
- `weightedCTranslatedCenter` is the image of the split-center subgroup
  `C_M` in `levi χ`. It is normal and central, and by
  `weightedCTranslatedCenter_eq_range` it is the image of the split
  component composed with the inverse of `weightedCParameterIso`.
  `weightedCTranslatedCenter_isActual` packages this as
  `IsActualSplitCenter`.
- `weightedCTranslatedMeasure` is the pushforward of a Haar measure on
  `M / C_M` along the induced quotient isomorphism. It is a Haar measure,
  invariant under inversion (`weightedCTranslatedMeasure_invInvariant`).
  `weightedCTranslated_isSquareIntegrable` carries square integrability
  modulo `C_M` over to the conjugate representation and this measure.

The scheme isomorphism, the quotient isomorphism and the Haar pushforward
are derived transports. Waldspurger does not state them: he works with
`s · M` and the representation `sω` directly.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333;
source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- I.1, printed pp. 238–241: the split center `A_M` (p. 239), the
  characters `|χ|_F` of rational characters and `X(M)` (p. 239), and the
  Haar convention `mes(H ∩ K) = 1` (p. 240). The two density parameters
  are unramified characters in the sense of p. 239.
- I.3, printed pp. 243–244: normalized induction (p. 243), induction in
  stages (pp. 243–244), and the conjugate representation
  `wπ'(g) = π'(w⁻¹ g w)` on the same space (p. 244). This last formula is
  the identity-carrier comparison `weightedCTranslatedCoefficientEquiv`.
- III.1, printed p. 263: square integrability modulo the split center,
  transported by `weightedCTranslated_isSquareIntegrable`.
- V.1, printed pp. 288–289: the parabolics `P_s = (M' ∩ s·P)U'` and
  `P̃_s = (M' ∩ s·P)Ū'` and the representation `sω` of `s · M` in the
  definition of `c_{P'|P}(s, ω)`.
- V.2, printed pp. 292–294: the weight `μ^G(ω) μ^{M'}(sω)⁻¹` of
  Corollary V.2.3 (p. 294). Its two density arguments are the parameters
  compared in `weightedC_restrict_ambientDensity` and
  `weightedC_restrict_lowerDensity`.
