# Euler polynomials at negative exponents through an inverse line bundle

Lean module: `Langlands.AlgebraicGeometry.Picard.InverseLineBundleEulerPolynomial`.

This helper module serves the proof of
`Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement`
(`χ(M) = (-1)^g χ(N)` when `N ⊗ M` is trivial on a `g`-dimensional abelian variety).
The target is formula (7) with `m = -1` of Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary version), (9.11), printed p. 131. The proof in
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof` avoids
their Hirzebruch–Riemann–Roch argument; instead it uses polynomiality in the exponent and a
product identity. That argument has two formal parts, which this module proves:

1. `n ↦ χ(N^n)` is one polynomial in `n ∈ ℤ`. Negative powers are realised by the inverse
   bundle: the value at `-n` is `χ(M^n)`, and also `χ(Mn)` for every module `Mn` with
   `N^n ⊗ Mn` trivial.
2. A polynomial identity `P(k) P(-k) = c k^(2g)` for all `k ≥ 1` gives `P(-1) = (-1)^g P(1)`.

The geometric input, the product identity `χ(N^k) χ(M^k) = c k^(2g)`, is not proved here;
the proof module takes it from the published theorem
`Langlands.AbelianScheme.algClosedFieldAmpleEulerInverseScaling`.
All results are derived. The three `def`s construct isomorphisms of modules and introduce
no new mathematical notion, and no declaration is a new statement target. Every theorem uses
only published Library results and Mathlib, and its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Conventions

`tensorObj`, `tensorPow`, `structureSheaf`, `LineBundle`, `HasFiniteCohomology` and
`eulerCharacteristic` are the Library notions that the target statement uses:
`tensorPow F n` is the `n`-fold tensor power with `tensorPow F 0 = 𝒪_X`, and
`eulerCharacteristic f F h` is the integer `Σ (-1)^i dim_K H^i(X, F)` of the relative
cohomology of `f : X ⟶ Spec K`. Euler characteristics are cast to `ℚ` when they are
compared with polynomial values.

## Declarations

### `Langlands.Scheme.Modules.tensorPowInverseCancelIso`

For `𝒪_X`-modules `M`, `N` and an isomorphism `e : M ⊗ N ≅ 𝒪_X`, this gives, for all
natural numbers `k` and `j`, an isomorphism `M^k ⊗ N^(j+k) ≅ N^j`.
It is defined by recursion on `k`:
- for `k = 0` it is the left unitor `𝒪_X ⊗ N^j ≅ N^j`;
- for `k + 1` it is the middle-four interchange
  `(M ⊗ M^k) ⊗ (N ⊗ N^(j+k)) ≅ (M ⊗ N) ⊗ (M^k ⊗ N^(j+k))`
  (`tensorMiddleFourIso`). It then applies `e` to the first factor and the recursive
  isomorphism to the second, and ends with the left unitor.

This is a construction (`def`) of an isomorphism, not a new mathematical notion.

### `Langlands.Scheme.Modules.tensorPowInverseIso`

For `𝒪_X`-modules `N`, `M` and `e : N ⊗ M ≅ 𝒪_X`, this gives, for every natural number `n`,
an isomorphism `N^n ⊗ M^n ≅ 𝒪_X`. It is defined by recursion on `n`:
- for `n = 0` it is the left unitor `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`;
- for `n + 1` it is the middle-four interchange
  `(N ⊗ N^n) ⊗ (M ⊗ M^n) ≅ (N ⊗ M) ⊗ (N^n ⊗ M^n)`. It then applies `e` to the first factor
  and the recursive isomorphism to the second, and ends with the left unitor
  `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`.

This is a construction (`def`) of an isomorphism, not a new mathematical notion.

### `Langlands.Scheme.Modules.inverseUniqueIso`

For `𝒪_X`-modules `A`, `B`, `B'` with `e : A ⊗ B ≅ 𝒪_X` and `e' : A ⊗ B' ≅ 𝒪_X`, this is
the isomorphism `B' ≅ B` given by the chain
`B' ≅ 𝒪_X ⊗ B' ≅ (B ⊗ A) ⊗ B' ≅ B ⊗ (A ⊗ B') ≅ B ⊗ 𝒪_X ≅ B`.
The steps are: the inverse of the left unitor; the inverse of `tensorComm B A ≪≫ e` on the
first factor; the associator `tensorAssociator`; `e'` on the second factor; and the right
unitor. So any two inverses of a module are isomorphic.

This is a construction (`def`) of an isomorphism, not a new mathematical notion.

### `Langlands.AlgebraicGeometry.Picard.coherentEulerSequence_tensorPow_inverse`

Let `f : X ⟶ Spec K` be proper over a field. Let `N`, `M` be line bundles and
`e : M ⊗ N ≅ 𝒪_X`. Then the term at `j + k` of the Library's Euler sequence of the
coherent sheaf `M^k` twisted by `N` (`coherentEulerSequence f (M^k) _ N (j + k)`, which is
`χ(M^k ⊗ N^(j+k))`) equals `χ(N^j)`.
Proof: unfold the sequence term to the Euler characteristic of `M^k ⊗ N^(j+k)` and transport
it along `tensorPowInverseCancelIso` (`eulerCharacteristic_eq_of_iso`).

### `Langlands.AlgebraicGeometry.Picard.coherentEulerSequence_tensorPow_zero`

The term at `0` of the same sequence is `χ(M^k)`, by the right unitor
`M^k ⊗ 𝒪_X ≅ M^k`. The finiteness proof on the right-hand side is arbitrary.

### `Langlands.AlgebraicGeometry.Picard.lineBundleEulerPolynomial_eval_neg`

**Statement.** Let `X` be Noetherian and separated, `f : X ⟶ Spec K` proper over a field,
and `topologicalKrullDim X ≤ d`. Let `N`, `M` be line bundles on `X` with
`e' : M ⊗ N ≅ 𝒪_X`. Then for every `k : ℕ` and every finiteness proof, the Library's Euler
polynomial `lineBundleEulerPolynomial f N d` takes the value `χ(M^k)` at `-k`.

**Proof.** Write `P := lineBundleEulerPolynomial f N d`. The Library's
`coherentEulerPolynomial f (M^k) _ N d` is the polynomial of the coherent sheaf `M^k`
twisted by `N`. Its support-dimension hypothesis `HasSupportDimensionLT (M^k) (d + 1)`
follows from the dimension bound (`HasSupportDimensionLT.of_topologicalKrullDim_le`).
This polynomial equals `P.comp (X - k)`: at each of the infinitely many rationals `j + k`,
where `j : ℕ`, both sides are `χ(N^j)`. The left side is so by `coherentEulerPolynomial_eval`
and `coherentEulerSequence_tensorPow_inverse`; the right side is so by
`lineBundleEulerPolynomial_eval`. Hence they agree (`Polynomial.eq_of_infinite_eval_eq`).
Evaluating at `0` gives `P(-k) = χ(M^k)` by `coherentEulerSequence_tensorPow_zero`.

### `Langlands.AlgebraicGeometry.Picard.exists_inverseLineBundleEulerPolynomial`

**Statement.** Let `X` be Noetherian and separated, `f : X ⟶ Spec K` proper over a field,
and `topologicalKrullDim X ≤ d`. Let `N`, `M` be line bundles on `X` with
`Nonempty (N ⊗ M ≅ 𝒪_X)`. Then there is `P ∈ ℚ[X]` with `natDegree P ≤ d` such that, for
every `n : ℕ` and every finiteness proof:
- `P(n) = χ(N^n)` and `P(-n) = χ(M^n)`;
- `P(-n) = χ(Mn)` for every `𝒪_X`-module `Mn` with `Nonempty (N^n ⊗ Mn ≅ 𝒪_X)`. Here
  `Mn` is any module, not assumed to be a line bundle, and its finiteness proof is
  arbitrary.

**Proof.** Take `P := lineBundleEulerPolynomial f N d`. The degree bound and the values at
`n ≥ 0` are the Library lemmas `lineBundleEulerPolynomial_natDegree_le` and
`lineBundleEulerPolynomial_eval`. The values `P(-n) = χ(M^n)` are
`lineBundleEulerPolynomial_eval_neg`, applied to `e' := tensorComm M N ≪≫ e`. For the last
clause, let `e₂ : N^n ⊗ Mn ≅ 𝒪_X`. Then `inverseUniqueIso (tensorPowInverseIso N M e n) e₂`
is an isomorphism `Mn ≅ M^n`. So `χ(Mn) = χ(M^n)` by `eulerCharacteristic_eq_of_iso`, and
this equals `P(-n)` by the previous clause. The finiteness proof for `M^n` used here is
`lineBundleTensorPow_hasFiniteCohomology`.

### `Langlands.AlgebraicGeometry.Picard.polynomial_eval_neg_one_of_eval_mul_eval_neg`

**Statement.** Let `g : ℕ`, `P ∈ ℚ[X]` and `c ∈ ℚ`. Suppose
`P(k) P(-k) = c k^(2g)` for every natural number `k ≥ 1`. Then
`P(-1) = (-1)^g P(1)`. There is no degree hypothesis.

**Proof.**
- Both `P(X) · P(-X)` (`P * P.comp (-X)`) and `c X^(2g)` take the same values at the
  infinitely many points `1, 2, 3, …`. Hence `P(X) P(-X) = c X^(2g)`.
- If `c = 0`, then `P(X) P(-X) = 0` in the domain `ℚ[X]`, and `simp` reduces this to
  `P = 0`. Both sides of the goal are then `0`.
- If `c ≠ 0`, then `C c` is a unit, so `P ∣ X^(2g)`. Since `X` is prime (`prime_X`),
  `dvd_prime_pow` makes `P` associated to some `X^i`. Units of `ℚ[X]` are nonzero constants
  (`Polynomial.isUnit_iff`), so `P = a X^i`.
- The hypothesis at `k = 1` gives `a · (-1)^i a = c`, so `a² (-1)^i ≠ 0`. At `k = 2` it
  gives `a · 2^i · a · (-2)^i = c · 2^(2g)`. Together these give
  `a² (-1)^i 4^i = a² (-1)^i 4^g`, so `4^i = 4^g`, i.e. `2^(2i) = 2^(2g)`, and `i = g`
  (`Nat.pow_right_injective`).
- Finally, `P(-1) = a (-1)^g = (-1)^g P(1)`.

### `Langlands.AbelianScheme.field_exists_inverseLineBundleEulerPolynomial`

**Statement.** Let `K` be any field and `A` an abelian scheme over `Spec K` with
`A.HasRelativeDimension g`. Let `N`, `M` be line bundles on `A.X.left` with
`Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left)`. Then there is
`P ∈ ℚ[X]` with `natDegree P ≤ g` such that, for all finiteness proofs:
- `P(n) = χ(N^n)` and `P(-n) = χ(M^n)` for every `n : ℕ`;
- `P(-n) = χ(Mn)` for every `n : ℕ` and every module `Mn` on `A.X.left` with
  `Nonempty (tensorObj (tensorPow N.obj n) Mn ≅ structureSheaf A.X.left)`;
- `P(1) = χ(N)` and `P(-1) = χ(M)`. These use `N.obj` and `M.obj` themselves, with
  Euler characteristics `eulerCharacteristic A.X.hom N.obj _` and
  `eulerCharacteristic A.X.hom M.obj _`, the spelling of the target statement.

**Proof.** `A.X.left` is Noetherian and separated (`field_isNoetherian`,
`field_isSeparated`), and its topological Krull dimension is `g`
(`field_topologicalKrullDim`). Apply `exists_inverseLineBundleEulerPolynomial` with
`f = A.X.hom` and `d = g`; `A.X.hom` is proper because `A` is an abelian scheme. This
gives the first three clauses. The two values at `±1` follow from the values at `n = 1` via `tensorPowOneIso : F^1 ≅ F` and
`eulerCharacteristic_eq_of_iso`.

### `Langlands.AbelianScheme.field_eulerCharacteristic_inverse_of_mul_eq`

**Statement.** In the setting of the previous theorem, let `c : ℤ` and suppose that for every
natural number `k ≥ 1` and all finiteness proofs,
`χ(N^k) · χ(M^k) = c · k^(2g)` in `ℤ`. Then for all finiteness proofs `hN`, `hM`,
`eulerCharacteristic A.X.hom M.obj hM = (-1)^g * eulerCharacteristic A.X.hom N.obj hN`.
This is the conclusion of the target statement, under the extra product hypothesis.

**Proof.** Take `P` from `field_exists_inverseLineBundleEulerPolynomial`. The hypothesis
becomes `P(k) P(-k) = c k^(2g)` over `ℚ` for `k ≥ 1`. Apply
`polynomial_eval_neg_one_of_eval_mul_eval_neg`, rewrite `P(-1) = χ(M)` and `P(1) = χ(N)`,
and cast back to `ℤ`.

## Scope

- The field `K` is arbitrary: algebraic closure is not used. The dimension `g` may be `0`.
- No ampleness, symmetry or duality is assumed.
- The product hypothesis of `field_eulerCharacteristic_inverse_of_mul_eq` is the deep
  geometric input, which this module does not supply. For a non-degenerate line bundle `L`,
  Edixhoven–van der Geer–Moonen compute `χ(Λ(L))` in two ways (printed pp. 131–132,
  formulas (9)–(12)). Formula (9) gives `χ(Λ(L)) = (-1)^g deg(φ_L)`, and the first two
  equalities of (12) give `χ(Λ(L)) = χ(L) χ(L^{-1})`. Applying this to `L^k` and using
  `deg(φ_{L^k}) = k^(2g) deg(φ_L)` gives the hypothesis with `c = (-1)^g deg(φ_L)`.
