# Arithmetic pair L-factors at unramified places

Supporting module of Task 5003 (module
`Langlands.Automorphic.AssociatedGammaUnramifiedMatch`, namespace
`Langlands.ClassField.Global.RelativeWeilGroup`). It computes the arithmetic side of the
outside-set matching used in the proof of `AssociatedGammaStatement` (Henniart 2000,
Théorème 2.3): at a finite place where `S`, `S'` and the twisting Hecke character are
unramified, the arithmetic pair L-factor of the twisted pair is the reciprocal of
`∏ (1 - χ_z(ϖ) a b X)` over the Frobenius eigenvalues. Internal deduction from Library results.

## Results

- `multiplicativeConductor_quasicharacterCongr`: transport along an equality of topological
  data does not change the multiplicative conductor (`subst`).
- `isUnramifiedCharacter_quasicharacterBase`: if the Hecke character `χ` is unramified at `z`
  (`IsUnramifiedAt`), the transported local component `quasicharacterBase z χ_z` is an
  unramified character for the canonical topological data. The proof follows the published
  `multiplicativeConductor_eq_zero_of_isUnramifiedAt`: units of valuation `1` are integral
  units (`mem_localIntegers_iff`, `mem_integers_iff_discreteValuation_le_one`), after
  rewriting the canonical data by `topologicalData_eq_canonicalTopologicalData`.
- `localTwistCharacter_inertia`: the local twist character of an unramified `χ` is trivial on
  inertia (`weilCharacter_trivial_on_inertia_iff`, with the base candidate geometric by
  `isGeometricReciprocity_of_isBaseReciprocity`).
- `localTwistCharacter_localGeometricFrobenius`: at the geometric Frobenius its value is
  `χ.finiteUniformizerValue z` (`weilCharacter_localGeometricFrobenius`).
- `prod_linear_comp_C_mul_X`: substituting `aX` in `∏ (1 - r X)` scales the roots by `a`.
- `arithmeticPairLFactor_twist_of_unramified` (main): along a local relative Weil map `ι`, if
  `χ` is unramified at `z`, the local components of `S`, `S'` are unramified, and their Euler
  polynomials at the geometric Frobenius are `∏_(r ∈ s) (1 - r X)` and `∏_(r ∈ t) (1 - r X)`,
  then the arithmetic pair L-factor of `((χ ∘ τ_F) ⊗ S, S')` is
  `(∏_((a,b) ∈ (χ_z(ϖ) s) × t) (1 - a b X))⁻¹`. Proof: the twisted class is the class of the
  twisted local component (`localPairClass_twist_eq`); the tensor has zero monodromy and
  trivial inertia action, so its Weil–Deligne Euler polynomial is that of the Frobenius
  operator (`eulerPolynomial_eq_of_monodromy_eq_zero`); that operator is
  `(χ_z(ϖ) S(ι Fr)) ⊗ S'(ι Fr)`, whose Euler polynomial is given by the lemma
  `eulerPolynomial_tensorMap` together with `eulerPolynomial_smul`.
