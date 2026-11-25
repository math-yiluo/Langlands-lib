# Maximality of the prime describing a local ring of a normalized base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreMaximalPrime`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

If `T` is integral over a domain `O` of dimension at most one, a prime `q` of `T` whose localization `T_q` is a discrete valuation ring is maximal. The file applies this to the description, from another file, of the local rings of the normalization of the base change of `X` along `Spec B ⟶ Spec A` as localizations of an integral closure, as needed in the reduced fibre theorem (Tag 09IL).

## Main results

- `Ideal.isMaximal_of_isIntegral_of_isDomain_localizationAtPrime`: for `O` a domain with `Ring.DimensionLEOne`, `T` integral over `O`, and `q` prime in `T` with `T_q` a domain and not a field, `q` is maximal.
- `Ideal.isMaximal_of_isIntegral_of_ringEquiv_isDiscreteValuationRing`: the same when `T_q` is given by a ring isomorphism `D ≃+* T_q` from a discrete valuation ring `D`.
- `Scheme.exists_isMaximal_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`: let `W` be the base change of `X` along `Spec B ⟶ Spec A` (`B` finite flat over `A`), every quasi-compact open of `W` having finitely many irreducible components (`hW`); let `K` be the localization of `A` at its non-zero-divisors and `L` that of `B` at their images, with `L` finite over `K`. Given a point `y` of the normalization of `W` over `w`, and the local ring of `X` below `w` identified, compatibly with the maps from `A`, with a domain `O` of dimension at most one with fraction field `F`, there is a *maximal* prime `p` of the integral closure of `O` in `(F ⊗[K] L) / nilradical` and an isomorphism of `𝒪_y` with the localization at `p`, compatible with the maps from `B` — provided `𝒪_y` is a discrete valuation ring.

## Proofs

`T_q` has a prime strictly below its maximal ideal, giving a prime `q₀ < q`. Over an integral extension comparable primes have distinct contractions, so `q ∩ O` is nonzero, hence maximal, and a prime lying over a maximal ideal in an integral extension is maximal. The scheme statement adds this to `exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`.

## Watch for

- The discrete-valuation-ring property of the stalk (and that it is a domain) is a hypothesis of the scheme statement; the file only notes where it holds in the reduced fibre theorem.
- The module comment speaks of a local base ring, but locality of `O` is not assumed.
- Maximality is needed because the solution property `IntegralClosureBaseChange.IsSolution` of Tag 09EN ranges over maximal ideals.
- The isomorphism in the second result points out of `D`, the direction in which the stalk identification provides it.

## References

Tags 09IL, 09EN, 00GS.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreMaximalPrime.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
