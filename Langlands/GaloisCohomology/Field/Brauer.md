# The Brauer group as the second cohomology of the units

`Langlands/GaloisCohomology/Field/Brauer.lean`, namespace `Langlands.GaloisCohomology`.

For a separable closure `L` of `K`: `Br(K) ≅ H²(Gal(L/K), Lˣ)`, with `H²` in the cochain model of
`Langlands.ProfiniteCohomology`.

## Declarations

- Instance `isSmoothRep_underlyingRep_discreteUnitsRepresentation`: the representation underlying
  the Library's discrete units module `discreteUnitsRepresentation K L` is smooth (it is
  `unitsModule K L`).
- `unitsModuleContinuousEquiv K L n : Hⁿ(Gal(L/K), Lˣ) ≃ₗ continuousUnitCohomology K L n`, for
  `L/K` Galois: the comparison `linearEquivContinuousCohomology` (from
  `isoContinuousCohomology`) with the Library's `Langlands.BrauerComparison.continuousUnitCohomology`,
  Mathlib's continuous cohomology of the discrete module `Lˣ`.
- `brauerEquiv K L : BrauerGroup K ≃+ H²(Gal(L/K), Lˣ)`, for `L` a separable closure of `K`: the
  Library's `Langlands.BrauerComparison.brauerContinuousEquiv` followed by the inverse of
  `unitsModuleContinuousEquiv`.
- `unitsModuleContinuousEquiv_brauerEquiv`, `brauerEquiv_symm_apply`: the transport lemmas
  between `brauerEquiv` and the Library's `brauerContinuousEquiv`.

Through these lemmas the Library's statements about `brauerContinuousEquiv` (scalar extension,
corestriction, local invariants) can be read in the cochain model.

## Source and licence

New file. The repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, proves
`Br(K) ≅ H²` itself (`brauerEquivH2`, in its `src/GroundTheory/Brauer/AbsoluteGalois.lean`, a
multiplicative isomorphism); that directory is not taken and
the Library's comparison is used instead.

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter X, §4,
  p. 156 (the Brauer group `B_k = H²(/k)`), and §5, Proposition 9 and the isomorphism
  `δ : A_k → B_k`, pp. 158–159 (comparison with central simple algebras; by the Remark on p. 159
  Serre's isomorphism is the opposite of the one given by crossed products).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VI, §3, Theorem (6.3.4), p. 351 (`H²(G(L|K), L^×) ≅ Br(L|K)`,
  `H²(K, K̄^×) ≅ Br(K)`).
