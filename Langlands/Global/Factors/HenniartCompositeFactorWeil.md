# Weil-side determinants and pair L-factors along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source.

* `Weil.Local.extensionResidueDegree_algEquiv`: an algebra isomorphism has relative
  residue degree one. `localDegreeInt_extensionWeilEquiv`: the Weil map of an algebra
  isomorphism preserves the integer degree.
* `FiniteRepresentation.determinantCharacterClass_restrictClass`: the determinant of a
  restriction is the restriction of the determinant.
* `LocalWeil.unitaryDeterminant_restrictUnitaryLatticeEquiv`: for `Φ : W_E ≃ₜ* W_F`,
  the virtual determinant of the pulled-back unitary class at `w` is the determinant
  at `Φ w`.
* `FiniteRepresentation.eulerPolynomial_invariants_restrict`,
  `Weil.Local.{mem_localInertia_iff, localDegreeInt_mul, localDegreeInt_inv,
  localDegreeInt_localGeometricFrobenius}` and `InertiaEuler.eulerPolynomial_restrict`:
  for a degree-preserving `Φ : W_E ≃* W_F`, inertia invariants and the inverse
  Frobenius characteristic polynomial are unchanged by restriction.
* `LocalWeil.{unitaryBasisPairClass_eq_classOf,
  unitaryBasisPairClass_restrictUnitaryBasisEquiv,
  arithmeticPairLFactor_restrictUnitaryBasisEquiv,
  unitaryPairLFactor_restrictUnitaryLatticeEquiv}`: the arithmetic pair L-factor of
  basis classes, and hence `unitaryPairLFactor` of unitary lattices, is unchanged by
  pullback along a degree-preserving `Φ`.

The two fields may lie over different primes `p` and `q`. This is needed because `K`
lies over `p` and `padicField v` over `residuePrime v`.
