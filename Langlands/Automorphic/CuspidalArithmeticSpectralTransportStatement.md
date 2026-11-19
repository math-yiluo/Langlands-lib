# Arithmetic pullback carries attached spectral systems

Proposition definition only; nothing is proved here.

## Statement

`Langlands.Automorphic.CuspidalArithmeticSpectralTransportStatement.{uK, uL, uV}`:
let `K : Type uK` and `L : Type uL` be number fields with compact adele
quotients, `e : K ≃+* L` a field isomorphism, `r` a natural number and `c` a
class of actual irreducible cuspidal realizations of `GL_(r+1)` over `L`. Let
`s` be a spectral system of rank `r + 1` on the finite places of `L` attached
to `c` (`CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uL, uV}`: some
actual spectral presentation of a representative of `c`, with local factors in
`Type uV`, has `s` as its system).

Then there is a spectral system `s'` of rank `r + 1` on the finite places of
`K` that is attached (`HasSpectralSystem.{uK, uV}`) to the pulled-back class
`CuspidalOperatorRealization.IsoClass.arithmeticComap e c`, such that for all
but finitely many finite places `v` of `K`, whenever `s'` is defined at `v` and
`s` is defined at the corresponding place `(finitePlaceEquiv e).symm v` of `L`
(the place `e(v)`), the two Euler polynomials agree:

`s'.eulerPolynomial v = s.eulerPolynomial ((finitePlaceEquiv e).symm v)`.

`finitePlaceEquiv e : FinitePlace L ≃ FinitePlace K` is the Library's ideal
pullback along the ring-of-integers isomorphism induced by `e`.

## Provenance

Internal statement (transport of structure). The arithmetic pullback
`arithmeticComap` of `OperatorArithmeticTransportClasses` pulls automorphic
forms back along the adelic isomorphism induced by `e`. Transporting an actual
spectral presentation (finite slice, local factors, restricted tensor
presentation, spherical Hecke spectra) along `e` should give a presentation of
the pulled-back realization whose unramified spectrum at `v` is the spectrum
of the original at `e(v)`. No source is cited for this identification; it is
the expected compatibility of the Library's constructions, stated here
because it is not yet proved.

It is the missing link between the two endpoints of a supplied isobaric chain
and actual data: `StartsAtCuspidal` and `terminal` in
`Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower` pull data back
along `bottomEquiv` and `topEquiv.symm`. Task 7784 (distinct Mackey components
from B6) needs it to compute the Euler polynomials at both ends of such a
chain.

## What is not asserted

The statement is one direction (from `c` to its pullback) and only up to
finitely many places. It does not assert that the transported system is
exactly `s` reindexed, that local components correspond, or anything about
ramified places.
