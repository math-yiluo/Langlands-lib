# The Herbrand quotient of the integral ideles (statements)

Author: Worker 226.

This module states two propositions and proves nothing.

## `CyclicIntegralIdeleHerbrand`

Let `F : Type u` and `E : Type v` be number fields in independent universes, with
`[Algebra F E]`, `[IsGalois F E]` and `[IsCyclic (E ≃ₐ[F] E)]`. Let `J∞` be the integral
ideles, i.e. the published `integralIdeles E` of `Langlands.ClassField.Global.IntegralIdeleCoefficients`:
ideles whose coordinate at every finite place of `E` has valuation one, with arbitrary
coordinates at the infinite places. The group `Gal(E/F)` acts through
`integralIdeleRepresentation F E`, and cohomology is the published
`integralIdeleCohomology F E n`, i.e. Mathlib's ordinary `groupCohomology`. The proposition
asserts:

`H¹(Gal(E/F), J∞)` and `H²(Gal(E/F), J∞)` are finite and
`Nat.card H² = archimedeanHerbrandFactor F E * Nat.card H¹`.

Here `archimedeanHerbrandFactor F E` is Worker 343's published `D∞`, the product over the
`Gal(E/F)`-orbits of infinite places of `E` of the stabilizer orders. In Herbrand-quotient
language this is `h(J∞) = D∞`. Finiteness is part of the conclusion. The degree-one
extension is included.

## `ArchimedeanCompletionHerbrand`

For number fields `F E : Type u` with `[Algebra F E]` and `[IsGalois F E]`, and an infinite
place `w` of `E`, let `D_w` be the stabilizer of `w` in `Gal(E/F)`. It acts on `E_wˣ` through
the published `infiniteLocalRepresentation F w` of `Langlands.ClassField.Global.IdeleArchimedean`.
The proposition asserts `HasHerbrandQuotient (infiniteLocalRepresentation F w) (Nat.card D_w)`,
in the sense of `Langlands.Cohomology.HerbrandQuotient`. That is: `H¹(D_w, E_wˣ)` and
`H²(D_w, E_wˣ)` are finite and `|H²| = |D_w| · |H¹|`.

## Provenance

The original statements are in E. Artin and J. Tate, *Class Field Theory* (2009), source
`artin-tate-2009-class-field-theory` (PDF page = printed page + 9), Chapter V §3, printed
p.13 (PDF p.22). For `S` a finite set of places containing the archimedean ones, Artin–Tate
compute `h2/1(J_S) = ∏_{p∈S} n_p` from `h2/1(∏_{P∉S} U_P) = 1` and the local values at the
places of `S`. `CyclicIntegralIdeleHerbrand` is the case `S` = the archimedean places, with
`J∞ = J_S`. Its product of local degrees `n_p` over the infinite places of `F` is written as
the product of stabilizer orders over the orbits of infinite places of `E`, which is
`archimedeanHerbrandFactor F E`. J. S. Milne, *Class Field Theory* v4.03 (2020), source
`milne-2020-class-field-theory`, Chapter VII Proposition 2.7, printed p.206 (PDF p.215),
gives the same formula `h(I_S) = ∏_{v∈S} n_v`.

`ArchimedeanCompletionHerbrand` is the local archimedean input: for a complex place over a
real one, `H¹ = 0` and `H²` has order `2` (from Artin–Tate's local theory, which gives
`h1 = 1` and `h2 = n_p`); for a split place `D_w` is trivial. The formulation with the
Library's stabilizer representation is internal. Choosing `S` to be exactly the infinite
places is Worker 343's route for `CyclicIdeleClassHerbrandQuotient` (task
`04294c5a-fea1-46f3-b7ea-e20d88ae0870`).
