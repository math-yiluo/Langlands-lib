# Harish-Chandra's Theorem 1.1 from its elliptic case and parabolic descent

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityReduction`
states, as `Langlands.HarmonicAnalysis.RegularOrbitalFourierRegularityReductionStatement.{u', v'}`,
the implication

`EllipticRegularOrbitalFourierRegularityStatement → RegularOrbitalFourierDescentStatement →
  RegularOrbitalFourierRegularityStatement`

(all at the universes `{u', v'}` of `F` and `A`), and proves it:
`Langlands.HarmonicAnalysis.RegularOrbitalFourierRegularityReduction.regularOrbitalFourierRegularityReduction`.
The two premises are the elliptic case of the local summability in Harish-Chandra's Theorem 1.1
(`Langlands.HarmonicAnalysis.UnitConjugation.EllipticRegularOrbitalFourierRegularityStatement`)
and its parabolic descent from the centralizer of an idempotent
(`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierDescentStatement`); the module
does not prove them. The conclusion is the local summability part of Theorem 1.1 for the unit
groups of finite-dimensional semisimple algebras over nonarchimedean local fields of
characteristic zero (`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityStatement`).

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15), §1:
printed p. 5 (PDF p. 20), "We shall prove this theorem by induction on `dim G`"; printed
pp. 10–11 (PDF pp. 25–26), the induction step for non-elliptic Cartan subalgebras ("Since
`A ≠ Z`, we have `dim M < dim G`. Hence, by the induction hypothesis …") and "So in order to
complete the proof of Theorem 1.1 we may assume that `h` is elliptic." The induction here is on
`dim_F A` instead of `dim G`, through the centralizers of idempotents.

## Proof

In the namespace `Langlands.HarmonicAnalysis.RegularOrbitalFourierRegularityReduction`:

1. `regularOrbitalFourierRegularityStatement_of_forall`: `RegularOrbitalFourierRegularityStatement`
   follows from `OrbitalFourierRegularityAt F A X` for every nonarchimedean local field `F` of
   characteristic zero, every finite-dimensional semisimple `F`-algebra `A` and every
   `X ∈ regularSet F A`; the two differ only in the order of the binders.
2. `orbitalFourierRegularityAt_of_isEllipticElement`: the elliptic case gives
   `OrbitalFourierRegularityAt F A X` for regular elliptic `X`, again by reordering binders.
3. `orbitalFourierRegularityAt_of_finrank_eq`: strong induction on `n = finrank F A`, for all
   finite-dimensional semisimple `A : Type v` of dimension `n` at once. Let `X` be regular. If
   `X` is elliptic, step 2 applies. Otherwise `not_isEllipticElement_iff` gives an idempotent
   `e` commuting with `X` and an element `a` such that `e a ≠ a e`. Let `M` be the centralizer of
   `e` (`Subalgebra.centralizer F {e}`, a type in the universe `v`), which contains `X`
   (`IdempotentCentralizer.mem_centralizer_singleton_iff`). By the module
   `Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer`:
   - `M` is a semisimple ring (`isSemisimpleRing_centralizer`);
   - `finrank F M < n` (`finrank_centralizer_lt`);
   - `X` is regular in `M` (`mem_regularSet_centralizer`, for the infinite field `F`, infinite
     because of characteristic zero).

   The induction hypothesis gives `OrbitalFourierRegularityAt F M X`, and the descent statement
   for `A`, `e` and `X` gives `OrbitalFourierRegularityAt F A X`.
4. `regularOrbitalFourierRegularityReduction`: steps 1 and 3 with `n = finrank F A`.

The proof uses the elliptic case only for the elements of the centralizers of idempotents that
are regular and elliptic there, and the descent statement only for non-central idempotents.
