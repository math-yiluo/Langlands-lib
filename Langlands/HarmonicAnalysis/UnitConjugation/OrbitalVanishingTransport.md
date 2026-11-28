# Vanishing of orbital integrals: transport between orbits

The module `Langlands.HarmonicAnalysis.UnitConjugation.OrbitalVanishingTransport` compares the
vanishing of orbital integrals at different points of the Lie algebra `A` of `Aˣ`. All
declarations are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

## Definitions

- `translateTest Z f`: the test function `Y ↦ f(Y + Z)`, on any topological additive group.
- `OrbitalVanishingAt X f`: `orbitalDistribution X ν hconv f = 0` for every Borel σ-algebra on
  the coset space of the centralizer of `X`, every Haar measure on `Aˣ`, every right-invariant
  Haar measure on the centralizer, every compatible quotient measure `ν` and every convergence
  proof. `regularOrbitalVanishing_iff`: `RegularOrbitalVanishing F A f` is
  `OrbitalVanishingAt X f` for every regular `X` (`Iff.rfl`).
- `OrbitMapVanishing H p hp f`: the same condition written for an orbit map `p : Aˣ → A`
  constant on the cosets `H g`, uniformly in the subgroup `H`.

## Results

- `orbitalVanishingAt_iff_of_homeomorph`: if a homeomorphism `φ` of `A` satisfies
  `φ(g⁻¹ X g) = g⁻¹ X' g` for every unit `g`, then `OrbitalVanishingAt X' f` holds exactly when
  `OrbitalVanishingAt X (f ∘ φ)` does. The proof shows that `X` and `X'` have the same
  centralizer (from `φ` injective and `X' = φ(X)`), rewrites both sides as `OrbitMapVanishing`,
  transports along the equality of the centralizers by substitution of a variable subgroup
  (`orbitMapVanishing_congr_subgroup`, `orbitMapVanishing_congr_fun`), and replaces the family
  of convergence conditions by the one of the pulled back test functions, `f' ↦ f' ∘ φ` being a
  bijection of the Schwartz–Bruhat space (`orbitMapVanishing_comp_homeomorph`).
- `orbitalVanishingAt_add_central_iff`: for central `Z`, the orbital integrals at `X + Z` are
  those of `translateTest Z f` at `X`; `add_central_mem_regularSet_iff`: `X + Z` is regular
  exactly when `X` is, as `ad(X + Z) = ad X` (`adjointEndomorphism_add_central`).
- `orbitalVanishingAt_smul_iff`: for a unit `s` of the field, the orbital integrals at `s • X`
  are those of `X ↦ f(s X)` at `X`; `smul_mem_regularSet_iff`: `s • X` is regular exactly when
  `X` is, since `ad(s X) = s · ad X` and scaling by `s ≠ 0` does not change the generalized
  `0`-eigenspace (`natTrailingDegree_charpoly_smul`, via Mathlib's
  `LinearMap.finrank_maxGenEigenspace_zero_eq`).
- `RegularOrbitalVanishing.translate_central`, `RegularOrbitalVanishing.scalarDilation`: `D₀` is
  stable under translation by central elements and under the dilations `f ↦ f_s`.
- `orbitalVanishingAt_congr`: the orbital integrals at `X` only depend on the values of `f` on
  the orbit of `X`; `orbitalVanishingAt_zero`, `OrbitalVanishingAt.add`,
  `OrbitalVanishingAt.smul`: the condition is linear in `f`.

## Source

The dilation stability is the second assertion of Harish-Chandra's Lemma 3.16: Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups*, with notes by S. DeBacker and
P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, §3.5, printed p. 28 (PDF p. 43):
"Suppose `f ∈ D₀` and `t ∈ Ω^×`. Then `f̂` and `f_t` are also in `D₀`."
