# The Euler characteristic of an inverse line bundle on an abelian variety

Lean module: `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof`.

The theorem `Langlands.AbelianScheme.algClosedFieldEulerInverseSymmetry` proves the Library
statement `Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement.{u}` exactly,
with no hypotheses. It uses two published Library theorems: the `k^(2g)` scaling theorem
`Langlands.AbelianScheme.algClosedFieldAmpleEulerInverseScaling` and the ample-existence
theorem `Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence`. The helper module
`Langlands.AlgebraicGeometry.Picard.InverseLineBundleEulerPolynomial` (its own paired
Markdown) supplies the polynomial algebra.

## Target

For an algebraically closed field `K`, an abelian scheme `A` over `Spec K` of relative
dimension `g`, and line bundles `N`, `M` on `A` with `N ⊗ M ≅ 𝒪_A`,
`χ(M) = (-1)^g χ(N)` in `ℤ`, for arbitrary finite-cohomology proofs. This is formula (7),
`χ(L^m) = m^g χ(L)`, with `m = -1`, in the proof of the Riemann–Roch theorem (9.11) of
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (preliminary version), printed
p. 131. The implemented proof does not follow the source's Hirzebruch–Riemann–Roch
argument; it is described below.

## Proof outline

1. **Ample case.** For an ample `H` with inverse `N`, the published scaling theorem
   `algClosedFieldAmpleEulerInverseScaling` gives
   `χ(H^k) χ(N^k) = k^(2g) χ(H) χ(N)` for all `k ≥ 1`. The helper module
   `InverseLineBundleEulerPolynomial` turns such a product identity into
   `χ(N) = (-1)^g χ(H)`.
2. **General case.** Fix an ample `H` with chosen inverse `H'`. For `N ⊗ M` trivial and
   all large `b`, the line bundle `P_b = N ⊗ H^b` is ample (`amplePowerTwist`) and
   `Q_b = M ⊗ H'^b` is an inverse of it, so step 1 gives `χ(Q_b) = (-1)^g χ(P_b)`. Both
   sides are values of the Library's coherent Euler polynomials in `b`; the identity at
   infinitely many `b` makes the polynomials agree, and evaluation at `b = 0` gives
   `χ(M) = (-1)^g χ(N)`.
3. **Ample existence.** The published theorem `algebraicallyClosedFieldAmpleExistence`
   supplies `H` over the algebraically closed field.

## Declarations

### `Langlands.AbelianScheme.coherentEulerSequence_zero_eq`

For `f : X ⟶ Spec K` proper over a field, a quasi-coherent `F` with finite affine
sections, a line bundle `L` and any finiteness proof `h` for `F`, the term at `0` of the
Library's Euler sequence `coherentEulerSequence f F _ L` (the Euler characteristic of
`F ⊗ L^0 = F ⊗ 𝒪_X`) equals `χ(F)` cast to `ℚ`. Proof: transport along the right unitor
`F ⊗ 𝒪_X ≅ F` with `eulerCharacteristic_eq_of_iso`.

### `Langlands.AbelianScheme.eulerCharacteristic_inverse_of_ample`

**Statement.** Let `K` be algebraically closed, `A` an abelian scheme over `Spec K` of
relative dimension `g`, `H` an ample line bundle, `N` a line bundle with `H ⊗ N ≅ 𝒪_A`, and
`hH'`, `hN'` finiteness proofs. Then `χ(N) = (-1)^g χ(H)`.

**Proof.** Apply `field_eulerCharacteristic_inverse_of_mul_eq` (helper module) to `H`, `N`
and `c = χ(H) χ(N)`. Its product hypothesis `χ(H^k) χ(N^k) = c k^(2g)` for `k ≥ 1` is the
published theorem `algClosedFieldAmpleEulerInverseScaling` (proving
`AlgClosedFieldAmpleEulerInverseScalingStatement`) with `Nk := N^k` (a line bundle by
`tensorPow_isLocallyFreeRankOne`) and the isomorphism `H^k ⊗ N^k ≅ 𝒪_A` given by `tensorPowInverseIso`, followed by commutativity
of multiplication in `ℤ`.

### `Langlands.AbelianScheme.eulerCharacteristic_inverse_of_ampleCase`

**Statement.** Let `K` be any field, `A` an abelian scheme over `Spec K` of relative
dimension `g`. Assume the ample case: for all line bundles `P`, `Q` with `P` ample,
`P ⊗ Q ≅ 𝒪_A` and all finiteness proofs, `χ(Q) = (-1)^g χ(P)`. Let `H` be an ample line
bundle. Then for all line bundles `N`, `M` with `Nonempty (N ⊗ M ≅ 𝒪_A)` and all finiteness
proofs `hN`, `hM`, `χ(M) = (-1)^g χ(N)`.

**Proof.**
- `A.X.left` is Noetherian and separated (`field_isNoetherian`, `field_isSeparated`) and
  its topological Krull dimension is at most `g` (`field_topologicalKrullDim`). Every line
  bundle on it has finite cohomology (`smoothProperLineBundleFiniteCohomology`).
- Let `H' := H.inverse` with `eH := H.tensorInverseIso : H ⊗ H' ≅ 𝒪_A`, and let `b₀` be
  given by `amplePowerTwist` for `H` and `N`.
- Let `P_N := coherentEulerPolynomial A.X.hom N _ H g` and
  `P_M := coherentEulerPolynomial A.X.hom M _ H' g`; by `coherentEulerPolynomial_eval` (with
  the support bound `HasSupportDimensionLT.of_topologicalKrullDim_le`) they take the values
  `χ(N ⊗ H^n)` and `χ(M ⊗ H'^n)` at every natural `n`.
- Claim `P_M = C((-1)^g) · P_N`. At each of the infinitely many rationals `j + b₀`
  (`j : ℕ`), set `P := N ⊗ H^(j+b₀)` and `Q := M ⊗ H'^(j+b₀)`, line bundles by
  `IsLocallyFreeRankOne.tensor` with `pullbackTensorComparisonIsIso` and
  `tensorPow_isLocallyFreeRankOne`. `P` is ample by `amplePowerTwist` (with the identity
  isomorphism). `P ⊗ Q ≅ 𝒪_A` is the composite of the middle-four interchange
  `tensorMiddleFourIso`, the given `N ⊗ M ≅ 𝒪_A` tensored with
  `tensorPowInverseIso H H' eH (j + b₀)`, and the left unitor. The ample case gives
  `χ(Q) = (-1)^g χ(P)`, i.e. the two sides agree at `j + b₀`; then
  `Polynomial.eq_of_infinite_eval_eq` proves the claim.
- Evaluate the claim at `0`: by `coherentEulerSequence_zero_eq` the values are `χ(M)` and
  `χ(N)` for the given proofs `hM`, `hN`. Cast back to `ℤ`.

### `Langlands.AbelianScheme.algClosedFieldEulerInverseSymmetry_of_ample`

**Statement.** `AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
AlgClosedFieldEulerInverseSymmetryStatement.{u}`.

**Proof.** Given `K`, `A`, `g`, `N`, `M` and the proofs, ample existence applied to the
commutative group object `A.toGrp` (smooth, proper and geometrically connected because `A`
is an abelian scheme) gives an ample `H`. Then `eulerCharacteristic_inverse_of_ampleCase`
with the ample case `eulerCharacteristic_inverse_of_ample` gives the conclusion.

### `Langlands.AbelianScheme.algClosedFieldEulerInverseSymmetry`

**Statement.** `AlgClosedFieldEulerInverseSymmetryStatement.{u}`: for every algebraically
closed field `K : Type u`, abelian scheme `A` over `Spec K` of relative dimension `g`, and
line bundles `N`, `M` on `A` with `Nonempty (N ⊗ M ≅ 𝒪_A)`,
`χ(M) = (-1)^g χ(N)` in `ℤ` for all finiteness proofs `hN`, `hM`.

**Proof.** Apply `algClosedFieldEulerInverseSymmetry_of_ample` to the published theorem
`Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence`, which proves
`AlgebraicallyClosedFieldAmpleExistenceStatement.{u}`.

## Scope

- No hypothesis beyond those of the target is added: every algebraically closed field of
  every characteristic, every `g` including `0`, all line bundles with trivial tensor
  product and arbitrary finiteness proofs.
- The module does not import `AlgClosedFieldAmpleMumfordEulerSquareStatement` or anything
  downstream of the target.
