# Pole regions of Weil–Deligne L-polynomials: the non-juxtaposed case

This module proves the second conjunct of the published
`Langlands.Global.WeilPairPoleRegionStatement`:

```lean
theorem Langlands.Global.nonJuxtaposedPoleRegionStatement :
    NonJuxtaposedPoleRegionStatement.{u, v, w}
```

The statement and its helper definitions (`lPolynomial`,
`HasNoReflectedCommonZero`, `AreJuxtaposed`) live in
`Langlands/Global/Factors/WeilPoleRegionStatement`, and this module does not
change them. The conclusion is the following. Let `σ` be isomorphic, as a
Weil–Deligne pair, to `⊕_{i : Fin k} ρ_i ⊗ Sp(n_i)`, where each `ρ_i` is
irreducible, each `n_i ≥ 1`, and no two blocks are juxtaposed. Let `B` be
irreducible and `σ' = (B, 0)`. Then the L-polynomial
`P_{σ⊗σ'}(X) = det(1 − XΦ | (ker N)^I)` and the reflected polynomial
`P_{σ^∨⊗σ'^∨}(q⁻¹X⁻¹)` have no common nonzero zero.

The first conjunct (the essentially unitary case) and the theorem for the full
conjunction are proved in separate modules.

## Provenance

This is Henniart (1986), *On the local Langlands conjecture for GL(n): the cyclic
case*, Ann. of Math. 123, Proposition 4.5(i), second hypothesis (printed p.160),
with its proof in §4.7 (printed pp.161–162). The implemented route follows that
argument as re-derived in the statement module's section "Why the statement
holds". Henniart reads off the zeros of each block factor from his 2.4 (8). The
Lean proof instead obtains eigenvectors and runs Schur's lemma on a twisted
intertwiner built from them, as described below. Every helper lemma is internal
to this proof.

## Structure of the Lean proof

The proof first works over an abstract group `G` with a normal subgroup `I`, an
element `Φ`, and a character `ν : G →* ℂˣ`. It is then specialized to the local
Weil group. All helpers live in the namespace
`Langlands.Global.WeilPoleRegionNonJuxtaposed`.

### 1. Factoring both polynomials over the blocks (section `Reduction`, `Generic`)

- `eulerPolynomial_tensor_of_equiv_directSum`: for `e : σ ≃ ⊕_i A_i`, the Euler
  polynomial of `σ ⊗ Z` is `∏_i` of the Euler polynomials of `A_i ⊗ Z`. The
  proof transports along `tensorEquiv e (refl Z)` and the Library's
  `tensorDirectSumLeft`, then applies `eulerPolynomial_directSum`. Throughout,
  `eulerPolynomial_eq_of_equiv` is the invariance of the Euler polynomial under
  pair isomorphism.
- `eulerPolynomial_tensor_dual_of_equiv_directSum`: the same product formula for
  `σ^∨ ⊗ Z`. Here `σ^∨` is transported to `⊕_i A_i^∨` along
  `(dualEquiv e).symm` and the Library's `AssemblyDual.dualDirectSumEquiv`.
- `eulerPolynomial_block_zeroMonodromy`: the factor of
  `(ρ ⊗ Sp(a+1)) ⊗ (B, 0)` equals `LocalFactor.eulerPolynomial` of
  `blockPairKernelOperator ν ρ B a 0 I Φ`. The zero-monodromy pair `(B, 0)` is
  replaced by `B ⊗ Sp(1)` (Library `blockOneEquiv`), and then the Library
  theorem `eulerPolynomial_block_block` applies with `b = 0`. This step needs
  `ν` trivial on `I`.
- `eulerPolynomial_dual_block_dual_zeroMonodromy`: the factor of
  `(ρ ⊗ Sp(a+1))^∨ ⊗ (B, 0)^∨` equals the Euler polynomial of
  `blockPairKernelOperator ν (ν^(1-(a+1)) ρ^∨) B^∨ a 0 I Φ`. The proof uses
  `Blocks.blockDualEquiv`, which gives `(ρ ⊗ Sp(m))^∨ ≅ (ν^(1-m) ρ^∨) ⊗ Sp(m)`,
  together with `dualZeroMonodromyEquiv` and `blockOneEquiv`.
- `eulerPolynomial_tensor_eq_prod` and `eulerPolynomial_tensor_dual_eq_prod`
  combine these for `σ ≃ ⊕_i block ν ρ_i n_i`, using `n_i ≥ 1`. The resulting
  factors are indexed by `n_i - 1`.

### 2. Eigenvectors from a vanishing factor (section `BlockEigen`)

`blockPairKernelOperator ν ρ B a 0 I g` acts on the single copy
`Fin (min (a+1) 1)` of `(ρ ⊗ B)^I` as `ν(g)^a` times the action of `g`.
`LocalFactor.eulerPolynomial_eval` gives `eval z = det(1 − z T)`, and
`LinearMap.bot_lt_ker_of_det_eq_zero` gives a nonzero kernel vector. From these:

- `exists_eigen_of_blockPair`: a zero `z` yields a nonzero `x ∈ ρ ⊗ B`, fixed by
  `I`, with `x = z ν(g)^a · g x`.
- `exists_eigen_of_dualBlockPair`: for the twisted dual factor with a character
  `χ` trivial on `I`, a zero `w` yields a nonzero `x ∈ ρ'^∨ ⊗ B^∨`, fixed by `I`
  under the untwisted action, with `x = w ν(g)^a χ(g) · g x`.

### 3. The twisted Schur argument (section `Core`)

`isIsomorphic_twist_of_eigenvectors` makes the following assumptions:

- every element is a power of `Φ` modulo `I`, and `ν` is trivial on `I`;
- `ρ`, `ρ'` and `B` are irreducible;
- `t ∈ ρ ⊗ B` and `s ∈ ρ'^∨ ⊗ B^∨` are nonzero, fixed by `I`, with
  `Φ t = c₁ t` and `Φ s = c₂ s`;
- `ν(Φ)^m c₁ c₂ = 1`.

It concludes `ρ' ≅ ν^m ρ`. The proof runs as follows.

- `zpow_eigen` and `eigen_of_mem`: if `g Φ^(-k) ∈ I`, then `g t = c₁^k t` and
  `g s = c₂^k s`, and `ν(g) = ν(Φ)^k`. Hence `(c_g d_g)⁻¹ = ν(g)^m`, where
  `c_g` and `d_g` are the scalars by which `g` acts on `t` and `s`.
- Contractions (section `Contraction`): `contrLeft t : ρ^∨ → B` and
  `contrRight t : B^∨ → ρ`, and `hs' = contrLeft s ∘ eval : ρ' → B^∨`. The
  lemmas `apply_contrLeft` and `apply_contrRight` express their pairings through
  `TensorProduct.dualDistrib`. `contrLeft_map` and `contrRight_map` describe how
  they interact with `TensorProduct.map`.
  `eq_zero_of_dualDistrib`: a tensor annihilated by every `α ⊗ β` is zero,
  because `dualDistribEquiv` is surjective.
- The range of `contrLeft t` is stable under `B`, and nonzero because `t ≠ 0`.
  By `stable_eq_bot_or_eq_top` it is everything (`B` irreducible). Therefore
  `contrRight t` is injective. Also `hs' ≠ 0` because `s ≠ 0`; the functionals
  `eval a ⊗ eval b` exhaust the double dual (`Module.evalEquiv`).
- `H = contrRight t ∘ hs' : ρ' → ρ` is nonzero and satisfies
  `H(ρ'(g) a) = ν(g)^m ρ(g) H(a)`. Its kernel is stable under `ρ'` and its
  range under `ρ`, so by irreducibility `H` is bijective. It is the required
  equivalence `ρ' ≅ twist (ν^m) ρ`, built with
  `Representation.IntertwiningMap.ofBijective`.

`not_isIsomorphic_twist_self`: an irreducible `ρ` is not isomorphic to `χρ`
when `‖χ(Φ)‖ < 1`. Conjugating `ρ(Φ)` gives
`det ρ(Φ) = χ(Φ)^(dim ρ) det ρ(Φ)`. Here `det ρ(Φ) ≠ 0` and `dim ρ ≥ 1`
(`nontrivial_of_isIrreducible`), so `‖χ(Φ)‖^(dim ρ) = 1`, a contradiction.

### 4. The abstract theorem (`not_common_zero`)

Assume `ν(Φ) = q⁻¹` with `q > 1`. Suppose the first polynomial vanishes at
`z ≠ 0` and the second at `q⁻¹ z⁻¹`. Some factor `i` of the first product and
some factor `j` of the second vanish (`Polynomial.eval_prod`,
`Finset.prod_eq_zero_iff`). Section 2 then gives the following eigenvectors:

- `t ∈ ρ_i ⊗ B` with `Φ t = (z ν(Φ)^(n_i - 1))⁻¹ t`;
- `s ∈ ρ_j^∨ ⊗ B^∨` with `Φ s = (q⁻¹ z⁻¹)⁻¹ s`. The twist exponents cancel:
  `ν(Φ)^(n_j-1) ν(Φ)^(1-n_j) = 1`.

These satisfy `ν(Φ)^(n_i) c₁ c₂ = 1`, so section 3 gives
`ρ_j ≅ ν^(n_i) ρ_i`. If `i ≠ j`, this is the first disjunct of juxtaposition,
which the hypothesis excludes. If `i = j`, then
`‖(ν^(n_i))(Φ)‖ = q^(-n_i) < 1`, and `not_isIsomorphic_twist_self` rules it out.

### 5. Specialization (section `Local` and the main theorem)

- `mul_inv_frobenius_zpow_mem_inertia`: for every `g` in the local Weil group,
  `g Φ^(-deg g)` lies in `localInertia F`. This is the argument of
  `localUnramifiedCharacterClassificationFor`, using
  `localGeometricFrobenius_degree`.
- `nonJuxtaposedPoleRegionStatement` applies `not_common_zero` with:
  - `ν = localNormCharacter F`, `I = localInertia F`,
    `Φ = localGeometricFrobenius F` and `q = residueCardinality F`;
  - `localNormCharacter_on_inertia`, `localNormCharacter_geometricFrobenius`
    and `residueCardinality_gt_one`;
  - the blocks `(ρ i).val`.

  The values of `localBlock`, `localParameterTensor`, `localParameterDual` and
  `localZeroMonodromyParameter` agree definitionally with the abstract pairs
  `block`, `tensor`, `dual` and `zeroMonodromy`. All hypotheses of the published
  statement are kept, including the universes `u, v, w`. Only the first
  disjunct of `AreJuxtaposed` is used.

The theorem depends only on the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.
