# Arithmetic pullback of isobaric data carries attached spectral systems

Worker 5130 wrote this module for Task 7784. It extends the cuspidal transport statement
`CuspidalArithmeticSpectralTransportStatement` from cuspidal classes to isobaric
constituent data. The module assumes that statement as a hypothesis `hP` and proves no
cuspidal transport itself.

## Contents

- `SpectralSystem.eulerPolynomial_eqRec`: casting a spectral system along a rank equality
  `h : n = m` keeps every Euler polynomial.
- `IsobaricData.map_arithmeticComap_eq`: if `σ : Fin k → PositiveRankCuspidalClass L`
  enumerates the constituents of `D` (`Finset.univ.val.map σ = D`), then
  `j ↦ (σ j).arithmeticComap e` enumerates those of `D.arithmeticComap e`.
- `IsobaricData.sum_rank_arithmeticComap_eq`: the ranks of this enumeration add up to the
  rank of `D.arithmeticComap e`.
- `IsobaricData.HasSpectralSystem.arithmeticComap`: assume `hP` and let `e : K ≃+* L` be an
  isomorphism of number fields (with compact adele quotients). If the spectral system `s`
  is attached to isobaric data `D` over `L`, then some spectral system `s'` is attached
  to `D.arithmeticComap e` over `K`. At all but finitely many finite places `v` of `K`
  where both are defined, the Euler polynomial of `s'` at `v` equals that of `s` at
  `(finitePlaceEquiv e).symm v`.

## Proof of the last item

Unfold the attachment of `s` to `D`: an enumeration `σ` of the constituents, attached
systems `t j` for the cuspidal classes `σ j`, and cofinite agreement of `s` with the direct
sum `finiteSum t`. Apply `hP` to each `σ j` and choose the systems `t' j` for the pulled-back
classes. Then `s'` is the direct sum of the `t' j`, cast to the rank of
`D.arithmeticComap e`, so it is attached to the pullback with the enumeration from
`map_arithmeticComap_eq`. For the Euler polynomials, `(finitePlaceEquiv e).symm` is
injective, so cofinite conditions on places of `L` pull back to cofinite conditions on
places of `K`. At cofinitely many `v`, the Euler polynomial of the direct sum is the product
over `j` (`finiteSum_eulerPolynomial`). Each factor matches by `hP`, and the product for
`t` matches `s`.

## Provenance

Euler polynomials of an isobaric sum are products of those of the constituents (Jacquet–
Shalika, as in the Library's isobaric data). The cuspidal transport along field
isomorphisms is the hypothesis `hP`, stated in `CuspidalArithmeticSpectralTransportStatement`.
Internal to the project.
