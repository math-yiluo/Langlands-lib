# Pole regions of Weil–Deligne L-polynomials: the essentially unitary case

This module proves the first conjunct of the published
`Langlands.Global.WeilPairPoleRegionStatement`:

```lean
theorem Langlands.Global.essentiallyUnitaryPoleRegionStatement :
    EssentiallyUnitaryPoleRegionStatement.{u, v, w}
```

The statement and its helper definitions (`lPolynomial`, `HasNoReflectedCommonZero`,
`IsEssentiallyUnitary`, `residueCardinality`) are in
`Langlands/Global/Factors/WeilPoleRegionStatement`, and this module leaves them
unchanged. The claim is as follows. Let `F` be a p-adic field and let `A`, `B` be
essentially unitary open-inertia representations of its local Weil group, with
`σ = (A, 0)` and `σ' = (B, 0)`. Then no nonzero `z` satisfies both
`P_{σ⊗σ'}(z) = 0` and `P_{σ^∨⊗σ'^∨}(q⁻¹ z⁻¹) = 0`. Here `P` is the Weil–Deligne
Euler polynomial `det(1 − XΦ | (ker N)^I)` at the chosen geometric Frobenius `Φ`,
and `q` is the residue cardinality.

The second conjunct, the non-juxtaposed case, and the theorem for the whole
conjunction live in separate modules.

## Provenance

The source is Henniart (1986), *On the local Langlands conjecture for GL(n): the
cyclic case*, Ann. of Math. 123, Proposition 4.5(i), first hypothesis (printed
p.160), proved in §4.7. The route is the modulus argument from the section "Why the
statement holds" of the statement module, carried out on single eigenvectors rather
than on whole invariant subspaces. Henniart argues with the absolute values of the
Frobenius eigenvalues of the summands, citing his 2.4 (7). Every helper lemma here is
internal to this proof and standard linear algebra. The helpers live in namespace
`Langlands.Global.WeilPoleRegionUnitary`.

## Helper lemmas

**Zeros give eigenvectors.**
- `exists_eigenvector_of_eulerPolynomial_eval_eq_zero`: let `T` be an endomorphism of a
  finite-dimensional complex space and `z ≠ 0`. If `LocalFactor.eulerPolynomial T`
  vanishes at `z`, then some `x ≠ 0` has `T x = z⁻¹ x`. Proof:
  `LocalFactor.eulerPolynomial_eval` rewrites the value as `det(1 − zT)`. A zero
  determinant gives a nonzero kernel vector `x` (`LinearMap.bot_lt_ker_of_det_eq_zero`),
  so `x = z T x`.
- `exists_kernel_eigenvector_of_eulerPolynomial_eval_eq_zero`: apply this to a
  Weil–Deligne pair `A`, normal subgroup `I` and element `g`. If
  `LocalFactor.WeilDeligne.eulerPolynomial A I g` vanishes at `z ≠ 0`, then some
  `x ≠ 0` in `A` satisfies `N x = 0`, `i x = x` for all `i ∈ I`, and `g x = z⁻¹ x`.
  Proof: the Euler polynomial is by definition the Euler polynomial of
  `LocalFactor.WeilDeligne.kernelOperator A I g` on the `I`-invariants of `ker N`.
  The previous lemma gives an eigenvector `y` there. Its underlying vector
  `y.val.val` has the stated properties, because both subtype inclusions are
  injective and commute with the action. The main proof uses only `x ≠ 0` and
  `g x = z⁻¹ x`.

**Eigenvalues on tensor products and duals.** Here `V`, `W` are finite-dimensional
complex spaces.
- `exists_eigenvector_of_rTensor_apply_eq` and `exists_eigenvector_of_lTensor_apply_eq`:
  if `S ⊗ 1` (resp. `1 ⊗ T`) has a nonzero vector with eigenvalue `c`, then `S`
  (resp. `T`) has a nonzero eigenvector with eigenvalue `c`. Proof: otherwise
  `S − c` is injective. Tensoring over a field preserves injectivity
  (`Module.Flat.rTensor_preserves_injective_linearMap`), so `(S − c) ⊗ 1` is
  injective and kills the given vector, a contradiction.
- `exists_eigenvalues_of_map_apply_eq`: if `S` is injective and `S ⊗ T` has a nonzero
  eigenvector `v` with eigenvalue `c`, then `c = αβ`, where `α` is an eigenvalue of `S`
  and `β` an eigenvalue of `T` (each with a nonzero eigenvector). Proof:
  `R = S ⊗ 1` commutes with `S ⊗ T` (`LinearMap.map_comp_rTensor`,
  `LinearMap.rTensor_comp_map`), so it preserves the nonzero eigenspace
  `U = ker(S ⊗ T − c)`. As `ℂ` is algebraically closed, `R|_U` has an eigenvector
  `u` with eigenvalue `α` (`Module.End.exists_eigenvalue`). `α ≠ 0` because `R` is
  injective. Since `S ⊗ T = (1 ⊗ T) ∘ R` (`LinearMap.lTensor_comp_rTensor`),
  `(1 ⊗ T) u = (c/α) u`. The previous lemmas turn `u` into eigenvectors of `S` for
  `α` and of `T` for `β = c/α`.
- `exists_eigenvector_of_dualMap_apply_eq`: an eigenvalue `c` of the transpose
  `f.dualMap`, with a nonzero eigenvector, is an eigenvalue of `f`. Proof: otherwise
  `f − c` is injective, hence surjective in finite dimension. A functional `ℓ` with
  `ℓ ∘ f = c ℓ` then vanishes on the image of `f − c`, which is everything, so `ℓ = 0`.

**Unitary eigenvalues.**
- `norm_eq_one_of_inner_smul_self`: for an inner-product core on a complex space, if
  `⟨c a, c a⟩ = ⟨a, a⟩` with `a ≠ 0`, then `‖c‖ = 1`. Proof: the left side is
  `c̄ c ⟨a, a⟩` and `⟨a, a⟩ ≠ 0`, so `c̄ c = 1`, giving `‖c‖² = 1`.
- `norm_character_mul_eigenvalue_eq_one`: if the twist `χ ⊗ A` is unitary
  (`FiniteRepresentation.IsUnitary`, an invariant `InnerProductSpace.Core`) and
  `g a = c a` with `a ≠ 0`, then `‖χ(g) c‖ = 1`. The twist acts on `a` by `χ(g) c`,
  so this is the previous lemma.

**Representation forms.**
- `exists_eigenvalues_of_tensor_apply_eq`: on `FiniteRepresentation.tensor A B`, `g`
  acts by `A(g) ⊗ B(g)`, and `A(g)` is injective (`Representation.apply_bijective`).
  So an eigenvalue of `g` on `A ⊗ B` is a product of eigenvalues of `g` on `A` and
  on `B`.
- `exists_eigenvector_of_dual_apply_eq`: on `FiniteRepresentation.dual A`, `g` acts by
  the transpose of `A(g⁻¹)`. So an eigenvalue of `g` on `A^∨` is an eigenvalue of
  `g⁻¹` on `A`.

## Proof of `essentiallyUnitaryPoleRegionStatement`

Suppose `z ≠ 0` is a common zero in the reflected sense. Write `Φ` for the local
geometric Frobenius and `q` for the residue cardinality. Then `1 < q`
(`Langlands.PadicField.TopologicalData.residueCardinality_gt_one`), so `q⁻¹ z⁻¹ ≠ 0`.

1. The tensor and dual parameters `localParameterTensor` and `localParameterDual` have
   the Weil–Deligne tensor and dual as their values. Their underlying representations
   are `FiniteRepresentation.tensor A B` and
   `FiniteRepresentation.tensor A^∨ B^∨`. The kernel-eigenvector lemma, applied to the
   two zeros, gives `x ≠ 0` in `A ⊗ B` with `Φ x = z⁻¹ x` and `y ≠ 0` in `A^∨ ⊗ B^∨`
   with `Φ y = (q⁻¹ z⁻¹)⁻¹ y`.
2. The tensor lemma factors `z⁻¹ = αβ`, where `α` and `β` are eigenvalues of `Φ` on
   `A` and on `B`. It also factors `(q⁻¹ z⁻¹)⁻¹ = α'β'`, where `α'` and `β'` are
   eigenvalues of `Φ` on `A^∨` and on `B^∨`. By the dual lemma, `α'` and `β'` are
   eigenvalues of `Φ⁻¹` on `A` and on `B`.
3. Choose characters `χ_A`, `χ_B` making the twists unitary, and put
   `c_A = χ_A(Φ)`, `c_B = χ_B(Φ)`. Then `χ_A(Φ⁻¹) = c_A⁻¹`. The unitary-eigenvalue
   lemma gives `‖c_A α‖ = ‖c_A⁻¹ α'‖ = ‖c_B β‖ = ‖c_B⁻¹ β'‖ = 1`.
4. The product of these four numbers is `αβ · α'β' = z⁻¹ · q z = q`. Taking norms
   gives `q = 1`, contradicting `1 < q`.
