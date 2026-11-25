# The Brauer sequence of a number field in the degrees above two

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees.lean`, namespace
`Langlands.GaloisCohomology`.

For every number field `K`, separable closure `Ω` and choice of embeddings `ι`:

* `unitsCohomologyHigherDegreesStatement`: **`H³(Gal(Ω/K), Ωˣ) = 0`, and for `r ≥ 4` the
  localization `Hʳ(Gal(Ω/K), Ωˣ) → ∏_{w real} Hʳ(Gal(K̄_w/K_w), K̄_wˣ)` is bijective**
  (`UnitsCohomologyHigherDegreesStatement` of `BrauerSequence/Proof.lean`);
* `brauerSequenceStatement`: **the fundamental exact sequence of the Brauer group** with its
  consequences, `BrauerSequenceStatement`, with no hypothesis.

## Complete types

```lean
Langlands.GaloisCohomology.unitsCohomologyHigherDegreesStatement : Langlands.GaloisCohomology.UnitsCohomologyHigherDegreesStatement
Langlands.GaloisCohomology.brauerSequenceStatement : Langlands.GaloisCohomology.BrauerSequenceStatement
```

## Outline of the proofs

The two halves are `subsingleton_cohomology_three_unitsModule`
(`BrauerSequence/HigherDegrees/DegreeThree.lean`) and `bijective_realBrauerLocalization`
(`BrauerSequence/HigherDegrees/RealDegrees.lean`); `brauerSequenceStatement_of_higherDegrees`
(`BrauerSequence/Proof.lean`) gives the Brauer sequence. The proofs work at finite Galois levels
`E ⊆ Ω`, with the Library's idèles `J_E`, idèle classes `C_E`, its global and local class field
theory (invariants, fundamental classes, Tate's theorem) and the cyclic layers of
`BrauerSequence/CyclicLayers.lean`; no direct limit of idèles over the levels is used.

## Declarations

`unitsCohomologyHigherDegreesStatement`, `brauerSequenceStatement`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.4, pp. 198–199.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), Chapter VIII, §1, Propositions (8.1.7), p. 430, and (8.1.20), p. 439.
