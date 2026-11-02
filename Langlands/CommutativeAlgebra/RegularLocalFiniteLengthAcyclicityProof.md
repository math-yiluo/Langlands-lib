# Proof of finite-length acyclicity over a regular local ring

Author: Worker 975. The statement `RegularLocalFiniteLengthAcyclicityStatement` is Worker
1015's.

Module `Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityProof`. The theorem

```text
Langlands.CommutativeAlgebra.regularLocalFiniteLengthAcyclicity :
  RegularLocalFiniteLengthAcyclicityStatement.{u}
```

proves the published proposition exactly. Let `R` be a regular local ring of Krull
dimension `g`. Let `C` be a bounded complex of finite free `R`-modules, zero in negative
degrees, whose homology modules are each killed by a power of the maximal ideal `m`. Then
`Hⁱ(C) = 0` for every `i < g`. The proof is the argument of Lemma (9.7) in Edixhoven,
van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), printed p.129 (PDF p.133), which
the source takes from Matsumura. The source's bound `C^j = 0` for `j > g` is not needed,
so the argument applies to any bounded complex in nonnegative degrees. Helper
declarations are in the namespace
`Langlands.CommutativeAlgebra.FiniteLengthAcyclicity`. There are no hypotheses beyond the
signatures and no proof holes; the module imports no algebraic geometry.

## The reduction sequence

For `x : R` and a complex `C` of `R`-modules:

- `quotientComplex x C` is the Library's degreewise scalar extension `baseChange` of `C` to
  `R ⧸ (x)`, and `restrictedQuotientComplex x C` is that complex regarded again over `R`
  by restriction of scalars.
- `quotientUnit x C : C ⟶ restrictedQuotientComplex x C` is the degreewise unit
  `m ↦ 1 ⊗ m` of the scalar-extension adjunction (the Library's `complexAdjunctionUnit`).
- `quotientSequence x C` is the short complex `C ⟶ C ⟶ restrictedQuotientComplex x C`,
  with first map `x • 𝟙 C`. Its composite vanishes because the unit is `R`-linear and `x`
  acts by zero on `R ⧸ (x)`.
- `unit_surjective` and `exists_smul_eq_of_unit_eq_zero`: for any `R`-module `M`, the
  unit `M ⟶ (R ⧸ (x)) ⊗ M` is surjective, and its kernel is `x M`. The proofs pass to the
  algebra tensor product through the Library's `extendScalarsAlgebraEquiv`, then use
  Mathlib's `TensorProduct.mk_surjective` and `TensorProduct.quotTensorEquivQuotSMul`
  (`(R ⧸ I) ⊗ M ≅ M ⧸ I M`).
- `quotientSequence_shortExact`: over a domain, for `x ≠ 0` and a complex of free modules,
  the sequence is short exact. Multiplication by `x` is injective on free modules over a
  domain, and the rest follows degreewise from the two previous lemmas.

## Consequences of the long exact sequence

- `homologyMap_smul_id`: multiplication by `x` on a complex induces multiplication by `x`
  on homology (through Mathlib's `ShortComplex.homologyMap_smul`).
- `smul_injective_homology`: if `H^{j-1}` of the reduction vanishes, multiplication by `x`
  is injective on `Hʲ(C)`. This is exactness of `H^{j-1}(C ⊗ R/x) ⟶ Hʲ(C) ⟶ Hʲ(C)`
  (Mathlib's `ShortExact.homology_exact₁`).
- `mul_le_annihilator_homology`: if `I₁` kills `Hⁱ(C)` and `I₂` kills `H^{i+1}(C)`, then
  `I₁ I₂` kills `Hⁱ` of the reduction. This uses exactness of
  `Hⁱ(C) ⟶ Hⁱ(C ⊗ R/x) ⟶ H^{i+1}(C)` (`homology_exact₃`).
- `restrictedQuotientHomologyIso`: the homology of the restricted complex is the
  restriction of the homology (`ShortComplex.mapHomologyIso` for the exact functor
  `restrictScalars`).
- `isStrictlyGE_quotientComplex`, `isStrictlyLE_quotientComplex`,
  `isFiniteFree_quotientComplex`: scalar extension preserves the degree bounds and finite
  free terms.
- `pow_le_annihilator_of_restrict`: if `m^N` kills the restriction of an `R ⧸ (x)`-module,
  then the `N`-th power of the maximal ideal of `R ⧸ (x)` kills the module. This holds
  because that maximal ideal is the image of `m`.
- `isZero_homology_of_neg`: a complex that is zero in negative degrees has zero homology
  there.

## The induction

`isZero_homology_of_lt_dim n` proves the statement for rings of dimension `n`, by
induction on `n`. For `n = 0` only negative degrees occur. Suppose `R` has dimension
`n + 1`. The Library gives that `R` is a domain (`regularLocalDomain`). It also gives a
prime `x ∈ m ∖ m²` (`RegularLocalFactorial.exists_prime_parameter`), with `R ⧸ (x)`
regular (`RegularLocalFactorial.isRegularLocalRing_quotient_span_singleton`) and of
dimension `n`; the dimension follows from `RegularLocalFactorial.spanFinrank_quotient_add_one`.
The reduction `quotientComplex x C` satisfies the hypotheses over `R ⧸ (x)`: its homology is
killed by `m^{N₁ + N₂}` by `mul_le_annihilator_homology`. By induction its homology vanishes
below degree `n`. Hence, for `i < n + 1`, multiplication by `x` is injective on `Hⁱ(C)`
(`smul_injective_homology`, using degree `i - 1 < n`). Since a power of `x ∈ m` kills
`Hⁱ(C)`, injectivity gives `Hⁱ(C) = 0`.
