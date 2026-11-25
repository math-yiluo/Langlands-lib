# Integrality of the conductors of every presentation of a local Weil representation: proof

This module proves `Langlands.Henniart.WeilConductorIntegralityStatement`
(`HenniartWeilConductorIntegralityStatement`):

```lean
theorem weilConductorIntegrality : WeilConductorIntegralityStatement.{uF, uV}
```

for every prime `p`, p-adic field `F : PadicField.{uF} p` and finite-dimensional complex
representation `A` of the local Weil group with carrier in `uV`. Its level parameters are those of
the statement, in the same order.

## Proof outline

- **Every presentation.** For a presentation `P` with surjective restriction `hP`, the expressions
  `P.artinConductor hP` and `P.swanConductor hP` are by definition
  `Ramification.Padic.artinConductorOfQuotient T F.Carrier π hP ρ P.kernel_le` and its Swan
  analogue, with `T` the canonical data of the finite extension `absoluteFiniteExtension F
  P.extension`, `π` the restriction of Weil inertia to its inertia group, and `ρ` the action of
  Weil inertia on `A`. The theorems `Ramification.Padic.exists_nat_artinConductorOfQuotient` and
  `exists_nat_swanConductorOfQuotient` (`LocalFactor/Ramification/ArtinExponent`) say that these
  are natural numbers. They rest on the finite theorem `finiteGaloisConductorIntegrality`
  applied over the fixed field of inertia, where the extension is Galois.
- **Continuous representations.** `HerbrandBridge.continuousWeilFiniteInertiaPresentation`
  (`Herbrand/WeilInertiaProof`) gives a presentation of a continuous `A`, and
  `HerbrandBridge.weilInertiaRestriction_surjective` gives surjectivity of the restriction to the
  inertia of every finite Galois subextension; the first clause then applies.

No continuity, common closure, reciprocity or choice of a presenting field beyond the given one is
used for the first clause.

## Declarations, in order

Name space `Langlands.Henniart`; variables `{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
{A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}`.

- `exists_nat_presentation_artinConductor (P : FiniteInertiaPresentation F A)
  (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
  ∃ a : ℕ, P.artinConductor hP = (a : ℚ)`.
- `exists_nat_presentation_swanConductor (P : FiniteInertiaPresentation F A)
  (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
  ∃ s : ℕ, P.swanConductor hP = (s : ℚ)`.
- `weilConductorIntegrality : WeilConductorIntegralityStatement.{uF, uV}`.

## Relation to the Weil-level existence theorem

`Langlands.Henniart.weilArtinConductorExistence`
(`HenniartWeilArtinConductorExistenceProof`) is derived from the second clause of this theorem.

## Literature

Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter VI, §2,
Theorem 1′ (printed p. 99): `f(χ)` is a non-negative integer for every character `χ` of the Galois
group of a finite Galois extension; Corollary 1′ (printed pp. 100–101) identifies `f(χ)` with the
weighted codimension sum that the Library takes as definition. Deligne, *Les constantes des
équations fonctionnelles des fonctions L*, LNM 349 (1973), §4.5, printed pp. 537–538, formulas
(4.5.2) and (4.5.4): the conductors of a Weil representation are computed on a finite quotient
`I/J` of inertia, independently of `J`.
