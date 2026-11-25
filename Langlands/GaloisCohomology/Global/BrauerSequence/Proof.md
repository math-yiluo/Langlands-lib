# The fundamental exact sequence of the Brauer group: assembly

`Langlands/GaloisCohomology/Global/BrauerSequence/Proof.lean`, namespace
`Langlands.GaloisCohomology`.

`UnitsCohomologyHigherDegreesStatement` is the proposition on the degrees above two: for every
number field `K`, separable closure `Ω` and choice of embeddings `ι`, `H³(Gal(Ω/K), Ωˣ) = 0`, and for
`r ≥ 4` the localization of `Hʳ(Gal(Ω/K), Ωˣ)` to the real places is a bijection onto the product of
the local groups (the fields `subsingleton_cohomology_three` and `bijective_realBrauerLocalization`
of `BrauerSequenceData`). It is proved in `Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees`
(`unitsCohomologyHigherDegreesStatement`), which with `brauerSequenceStatement_of_higherDegrees`
gives `brauerSequenceStatement`.

- `brauerLocalization_finite_support`: a global Brauer class is nonzero at only finitely many finite
  places.
- `brauerSequenceData_of_higherDegrees`: given the two statements on the degrees above two for `K`,
  `Ω`, `ι`, all of `BrauerSequenceData K Ω ι` holds; the other fields are proved with no hypothesis.
- `brauerSequenceStatement_of_higherDegrees`: `BrauerSequenceStatement` from
  `UnitsCohomologyHigherDegreesStatement`.

## Complete types

```lean
Langlands.GaloisCohomology.UnitsCohomologyHigherDegreesStatement : Prop

@Langlands.GaloisCohomology.brauerLocalization_finite_support : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      (Langlands.GaloisCohomology.brauerLocalization ι v 2) x ≠ 0}.Finite

@Langlands.GaloisCohomology.brauerSequenceData_of_higherDegrees : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω),
  Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 3) →
    (∀ (r : ℕ),
        4 ≤ r →
          Function.Bijective
            fun (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) r))
              (w : { w : NumberField.InfinitePlace K // w.IsReal }) =>
            (Langlands.GaloisCohomology.realBrauerLocalization ι (↑w) r) x) →
      Langlands.GaloisCohomology.BrauerSequenceData K Ω ι

Langlands.GaloisCohomology.brauerSequenceStatement_of_higherDegrees : Langlands.GaloisCohomology.UnitsCohomologyHigherDegreesStatement →
  Langlands.GaloisCohomology.BrauerSequenceStatement
```

## Outline of the proofs

The fields of `BrauerSequenceData`: `finite_support` and `sum_localInvariant_eq_zero` from
`localInvariant_finite_support_and_sum_eq_zero`, `eq_zero_of_brauerLocalization_eq_zero` from
`eq_zero_of_brauerLocalization_eq_zero'` (`Hasse.lean`); `existsUnique_brauerLocalization_eq` from
`existsUnique_brauerLocalization_eq'` (`Existence.lean`); `brauerRestriction_eq_zero` from
`brauerRestriction_eq_zero'` (`Restriction.lean`); `exists_isCyclic_dvd_localDegree` from
`CyclicLayers.lean`; the two fields on the degrees above two are the hypotheses.

## Declarations

`UnitsCohomologyHigherDegreesStatement`, `brauerLocalization_finite_support`,
`brauerSequenceData_of_higherDegrees`, `brauerSequenceStatement_of_higherDegrees`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. The
source proves the statement on the degrees above two as `subsingleton_cohomology_three_unitsLimitRep`
(`GlobalClassFormation.lean`), `bijective_realLocalization` (`GlobalClassFormation/HighUnits.lean`)
from its idèle limit modules; those are not ported (`HigherDegrees.lean` proves it without them).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Corollary (8.1.3), p. 428 (`H³(G, I_K) = 0`); Proposition (8.1.7), p. 430
  (`Hⁱ(k, I) ≅ ⊕_p Hⁱ(k_p, k̄_pˣ)` for `i ≥ 1`); Proposition (8.1.20), p. 439 (exactness of
  `0 → H²(k, k̄ˣ) → H²(k, I) → H²(k, C) → 0`): the route to the degrees above two.
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm 1962), p. 289 (`Hʳ(k, M) = 0` for `r > 2` over a nonarchimedean local
  field) and Theorem 3.1(c), p. 291 (`Hʳ(k_S, M) ≅ ∏_{real} Hʳ(k_P, M)` for `r ≥ 3`, the shape of
  the statement on the real places for finite modules).
