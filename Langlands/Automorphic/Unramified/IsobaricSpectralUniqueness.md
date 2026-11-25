# Uniqueness of the spectral systems attached to isobaric data

This module serves the proof of distinct Mackey components from B6 (module
`Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessReduction`). B6's
isobaric chains relate consecutive levels by `IsobaricData.IsWeakBaseChangeOf`. That relation
is existential: some system attached to the lower data and some system attached to the upper
data satisfy the numerical base-change identity. A computation that follows a chain from
level to level therefore has to identify different systems attached to the same data. This
module does that. It asserts nothing about existence of attached systems.

## Rank casts

`IsobaricData.IsWeakBaseChangeOf` compares `h ▸ t` with `s`, where `h` is an equality of
ranks. In namespace `Langlands.Unramified.SpectralSystem`:

- `exceptional_eqRec`: the cast `h ▸ s` has the exceptional set of `s`;
- `coe_eigenvalues_eqRec`: at every place where both are defined, the spectrum of `h ▸ s`,
  read as a multiset of `ℂˣ`, is the spectrum of `s`.

Both are proved by `subst h`.

## Cuspidal classes

`CuspidalOperatorRealization.IsoClass.HasSpectralSystem.eigenvalues_eq`: if `s` and `t` are
attached to the same cuspidal class `c` of rank `r + 1`, through presentations whose local
factors live in possibly different universes `uV` and `uW`, then
`s.eigenvalues v = t.eigenvalues v` at every finite place `v` outside both exceptional sets.
The proof chooses a representative `S` of `c` and presentations `P` and `Q` of `S` with
these systems (`hasSpectralSystem_iff`). It then applies the published
`CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`, uniqueness of the spherical
Hecke spectrum of a local component.

## Isobaric data

In namespace `Langlands.Automorphic.IsobaricData`:

- `eulerPolynomial_eq_of_hasSpectralSystem`: systems `t` and `t'` attached to equal
  positive-rank classes `c = c'` have equal Euler polynomials at every place where both are
  defined. The proof substitutes `c' = c` and applies the cuspidal statement.
- `HasSpectralSystem.sameEulerPolynomials`: two spectral systems `s` and `s'` attached to the
  same isobaric data `D` (`IsobaricData.HasSpectralSystem`, possibly in different universes
  `uV` and `uW`) have the same Euler polynomials outside a finite set
  (`SpectralSystem.SameEulerPolynomials`). By definition `s` agrees cofinitely with a finite
  sum of systems `t j` attached to the classes `σ j` of an enumeration `σ` of `D`, and
  likewise `s'` with `t' j'` for an enumeration `σ'`. Outside the union of the exceptional
  sets of all `t j` and `t' j'`, the proof sets `g c` to the Euler polynomial of `t j` for
  some chosen `j` with `σ j = c`. By the previous lemma each factor of the product for `t`
  is `g (σ j)`. Each factor of the product for `t'` is `g (σ' j')`, because every
  `σ' j'` occurs among the `σ j`. Both products are therefore `(D.map g).prod`. This avoids
  choosing a permutation between the two enumerations.
- `HasSpectralSystem.eventually_eigenvalues_eq`: consequently the two systems have equal
  spectra outside a finite set, since the Euler polynomial determines the spectrum
  (`Eigenvalues.eulerPolynomial_injective`).

## Provenance

The statements are internal consequences of the Library's definitions. The mathematical
input is uniqueness of the spherical spectrum of a local component, which the Library has
already proved.
