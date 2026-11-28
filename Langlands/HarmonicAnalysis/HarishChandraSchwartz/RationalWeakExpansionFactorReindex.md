# Comparing the auxiliary and ambient Levi data of a c-factor

Let \(n\) be a normalizer lift with \(nMn^{-1}\subseteq M'\). The
translated ambient cocharacter \(\chi\) is the defining cocharacter of
\(M\) followed by inner conjugation by \(n\). The auxiliary cocharacter
\(\psi_\alpha\) combines the conjugate cocharacter with a cocharacter
\(\alpha\) defining \(M'\), as in `RationalWeakExpansionCFamily`. Both
centralizers represent the translated Levi. The module compares their
parameter and coefficient identifications for use with the two auxiliary
parabolics of the c-family.

- `weightedC_factorCentralizer` combines `centralizer_auxiliary` with
  `weightedC_conjugatedCocharacter_eq` to identify the two centralizer
  subgroup functors.
- `weightedC_factorParameter_hom` compares the morphisms to the original
  standard Levi scheme. Postcomposition with the standard Levi inclusion
  detects equality by representability. On the ambient path,
  `parameterChangeIso_hom_comp` and `weightedCParameterIso_hom_comp` give
  the auxiliary centralizer inclusion followed by inverse conjugation.
  The defining `isoOfComap` for `factorParameterIso` gives the same
  composite by `SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp`.
- `weightedC_factorParameter_restrict` applies the preceding equality to
  rational points. It evaluates both unramified characters at the same
  point of the original Levi, using functoriality of `rationalPoints.map`.
- `weightedC_factorCoefficientEquiv` pulls the conjugated ambient
  coefficient back to the auxiliary Levi by `leviChange`. The resulting
  action of a point \(x\) is the original action at \(n^{-1}xn\), by
  `leviConjugation_apply_coe`, `leviChange_apply_coe`, and
  `standardLeviDynamicHomeomorph_apply_coe`. This is also the action of
  `conjugateRep` by `conjugationEquiv_apply`. The equivalence uses the
  identity on the complex carrier. The field and carrier universes are
  independent.

These are derived comparisons for Waldspurger's description of the
representation on \(s\cdot M\) in I.3, printed p. 244, and its use in the
two auxiliary integrals in V.1, printed pp. 288–289. The
scheme maps express the pullback of the unramified characters of I.1,
printed p. 239. [Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003)](https://doi.org/10.1017/S1474748003000082)
