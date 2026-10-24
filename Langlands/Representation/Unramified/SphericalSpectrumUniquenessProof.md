# Proof of the uniqueness of spherical principal-series spectra

Module `Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof`, namespace
`Langlands.Unramified`.

The main theorem is

`theorem sphericalSpectrumUniqueness : SphericalSpectrumUniquenessStatement.{uF, uV}`.

It proves the published statement of
`Langlands.Representation.Unramified.SphericalClassificationStatement` exactly, with both
universe parameters. Let `A` be an irreducible admissible object, and let `s` and `t` be
unordered spectra. If `HasSphericalSpectrum F A s` and `HasSphericalSpectrum F A t` both
hold, then `s = t` as multisets with all multiplicities. No Hecke-comparison statement or
other unproved prerequisite is used. The only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Route

1. **Forward scalars.** A spherical constituent of `I(z)` has the standard Hecke scalars of
   `ofTuple z` (Borel 1979, sections 7.1–7.2 and 10.4; Gross 1998, section 6). This is
   `hasSphericalHeckeSpectrum_of_isSphericalConstituent`, proved from the helper modules
   `MinusculeCosets`, `StandardHeckeSum` and `PrincipalSeriesHecke`.
2. **Separation.** The scalars on a nonzero fixed space determine the spectrum
   (`eq_of_hasSphericalHeckeSpectrum`).
3. **Main theorem.** Unfold both spectral relations to tuples `z` and `w` with
   `ofTuple z = s` and `ofTuple w = t`, apply step 1 to each constituent, and conclude by
   step 2.

## The Euler polynomial determines the spectrum

In namespace `Langlands.Unramified.Eigenvalues`:

- `eulerPolynomial_roots`: the roots of `eulerPolynomial s = ∏ (1 - z X)` form the multiset
  `s.map (fun z => z⁻¹)`. The proof writes `1 - C z X = C (-z) (X - C z⁻¹)`, splits off the
  nonzero constant (`roots_C_mul`), and uses `roots_multiset_prod_X_sub_C`.
- `eulerPolynomial_injective`: inversion of units is injective, so `Multiset.map_injective`
  recovers the multiset, and `Sym.ext` gives equality in `Eigenvalues n`.

## Generic transfer lemmas

These lemmas are stated for an arbitrary topological group `G` with representations
`ρ`, `σ` on complex vector spaces.

- `exists_fixed_lift`: let `f : ρ → σ` be a surjective intertwiner between smooth
  representations. Then every `K`-fixed vector of `σ` is `f` of a `K`-fixed vector of `ρ`,
  namely of `Hecke.fixedProjection` of any preimage. The proof uses
  `fixedProjection_intertwiner` and `fixedProjection_fixed`.
- `subrepresentationSubtype` is the inclusion of a subrepresentation as an intertwiner, and
  it is injective.
- `intertwiningMap_sum_translates`: `f (∑ ρ(x_α) v) = ∑ σ(x_α) (f v)`.
- `sum_translates_of_injective`: along an injective intertwiner, an identity
  `∑ σ(x_α) (f v) = c • f v` descends to `∑ ρ(x_α) v = c • v`.

## Forward scalars

`cornerAction_of_isSubquotientOf` is stated for any smooth representation `π` of
`GL_(r+1)(F)` that is a subquotient of `I(z)`, given by `S ⊆ I(z)` and a surjective
`f : S → π`. For a `K`-fixed `v` it shows

`cornerAction (standardHeckeElement F r i) v = standardHeckeScalar F (ofTuple z) i • v`.

The proof proceeds in four steps.

1. `S` is smooth by `isSmooth_of_injective` applied to its inclusion.
2. Lift `v` to a `K`-fixed `s' ∈ S` with `f s' = v` (`exists_fixed_lift`).
3. The inclusion of `s'` is a `K`-fixed vector of `I(z)`. So
   `principalSeries_sum_labelledRep` and `sum_translates_of_injective` give
   `∑_α S(x_α) s' = c • s'`.
4. By `standardHecke_cornerAction_eq_sum`, the corner action of `v` is
   `∑_α π(x_α) (f s') = f (∑_α S(x_α) s') = f (c • s') = c • v`.

`hasSphericalHeckeSpectrum_of_isSphericalConstituent` applies this to
`A.obj.representation`. Its statement,
`IsSphericalConstituent F z A → HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z)`, is
the implication of `SphericalConstituentHeckeScalarStatement`.

## Separation

`eq_of_hasSphericalHeckeSpectrum` takes a nonzero `K`-fixed vector. The two scalar
identities give `standardHeckeScalar F s i = standardHeckeScalar F t i` for every
`i ≤ r + 1` (`smul_left_injective`). Cancelling the nonzero factor `√q ^ (i (r + 1 - i))`
gives equal `elementaryCoefficient`s, hence equal coefficients of `X^i` for `i ≤ r + 1`.
Both Euler polynomials have degree `r + 1` (`eulerPolynomial_natDegree`), so the higher
coefficients vanish. Hence the Euler polynomials are equal, and `eulerPolynomial_injective`
gives `s = t`.
