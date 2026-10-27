# The dual-opposite form of product-Levi tempered sufficiency

Author: Worker 23.

This module proves

```text
theorem Langlands.glProductLeviDualOppositeTemperedSufficiency_of_core
    (h : GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV}) :
    GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV}
```

Both propositions are published in
[`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md),
with independent field and representation universes `uF` and `uV`. The first
is the upper generalized-exponent core statement and the second is the
opposite dual-eigenfunctional statement used by consumers. The theorem proves
only this one direction; it does not prove either proposition and does not
state their equivalence. Together with a proof of the core statement it
proves the dual-opposite statement.

## Notation

Fix an ordered block shape `C` of `n` and a refinement `D`. Write
`e(j,i) = C.flattenBlockEquiv D ⟨j, i⟩` for the flattened labels of `D`, and
`m_D(a)` for the image of the flattened block scalar
`(C.flatten D).blockScalarLevi F.Carrier a` under `flattenedLeviEquiv`. Let
`D' = reverseRefinement C D` be the refinement with `D' j = (D j).reverse`,
so the inner blocks of every outer block appear in reverse order. Write
`e'(j,i)` and `m'(c)` for the corresponding objects of `D'`. The inner index
types of `D j` and `D' j` are both `Fin (D j).length`.

## Declarations

Coordinate lemmas:

- `GeneralLinear.reindex_scalar`: relabelling the coordinates by an
  equivalence `Fin m ≃ Fin m'` fixes every scalar matrix.
- `GeneralLinear.BlockShape.reverseMatrix_conj_blockScalar`: conjugation by
  the block-reversal matrix `B.reverseMatrix R` sends
  `B.reverse.blockScalar R b` to `B.blockScalar R (fun k => b k.rev)`. The
  proof compares entries with the published `reverseMatrix_conjugate_entry`.
- `Geometric.flattenedLeviProductEquiv_blockScalarLevi` and
  `Geometric.flattenedLeviEquiv_blockScalarLevi_apply`: the outer component
  `i` of a flattened block scalar `c` is the inner block scalar of `S i` with
  entries `c (B.flattenBlockEquiv S ⟨i, j⟩)`, in the nested product and in
  the outer Levi respectively.
- `PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv`: the inner
  blocks of the image of `m` under `flattenedLeviEquiv` are the components of
  `flattenedLeviProductEquiv m`.

Translation between coinvariants:

- `Jacquet.conjTranslate ρ g h`: if `g u g⁻¹ ∈ N₂` for every `u ∈ N₁`, the
  linear map `Coinvariants ρ N₁ → Coinvariants ρ N₂` sending the class of `v`
  to the class of `ρ g v` (`conjTranslate_mk`).
  `conjTranslate_conjTranslate_inv` shows that translation by `g` undoes
  translation by `g⁻¹`.

In the namespace `ProductLeviDualOpposite`:

- `map_pow_sub_smul`: a linear map `L` with `L ∘ A = B ∘ L` satisfies
  `L ∘ (A - c • 1)^k = (B - c • 1)^k ∘ L`.
- `sum_mul_nonpos_of_antitone_of_nonneg`: summation by parts for a
  nonnegative antitone vector, described below.
- `reverseRefinement C D` and `reverseLabel C D`, the equivalence of flattened
  labels with `reverseLabel (e'(j,i)) = e(j, i.rev)` (`reverseLabel_apply`;
  `reverseLabel_symm_apply` is the inverse form).
- `reverseWeyl C D R : C.Levi R`, whose component `j` is
  `(D j).reverseMatrix R`. This permutation matrix reverses the order of the
  blocks of `D j` and keeps the order of coordinates inside each block.
- `conj_mem_refinedUnipotent_iff`: for `w = reverseWeyl C D R`,
  `w g w⁻¹ ∈ refinedUnipotent R C D` if and only if
  `g ∈ refinedOppositeUnipotent R C D'`. Componentwise this is the published
  `reverseMatrix_conj_mem_unipotentSubgroup_iff`.
- `reverseWeyl_conj_blockScalar`: `w m'(c) w⁻¹ = m_D(c ∘ (reverseLabel C D)⁻¹)`,
  from `reverseMatrix_conj_blockScalar` in each outer block.
- `toOpposite C D R ρ` and `fromOpposite C D R ρ`: for a representation `ρ`
  of `C.Levi R`, `toOpposite` is translation by `w⁻¹` from
  `RefinedJacquetModule C D ρ` to `RefinedOppositeJacquetModule C D' ρ`, and
  `fromOpposite` is translation by `w` in the other direction.
  `toOpposite_mk` gives the value on classes, and `fromOpposite_toOpposite`
  shows that `toOpposite` has a left inverse. Since `w` lies in `C.Levi R`,
  this uses the given action of `ρ`; no conjugated representation is
  introduced.
- `refinedLeviModulus_reverse`:
  `T.refinedLeviModulus C D' (m'(c)) = (T.refinedLeviModulus C D (m_D(c ∘ (reverseLabel C D)⁻¹)))⁻¹`.
  The proof applies the published `leviModulus_reverse` to each outer block.
- `refinedLeviHalfModulus_reverse`: as complex numbers, the positive half
  modulus `T.refinedLeviHalfModulus C D'` at `m'(c)` equals the inverse half
  modulus `T.refinedLeviInverseHalfModulus C D` at
  `m_D(c ∘ (reverseLabel C D)⁻¹)`.
- `toOpposite_normalizedRefinedJacquet`: `toOpposite` intertwines the upper
  normalized action of `m_D(c ∘ (reverseLabel C D)⁻¹)` with the opposite
  normalized action of `m'(c)`. On a class `q(v)` both sides are the same
  multiple of the opposite class of `ρ(w⁻¹ m_D(…)) v = ρ(m'(c) w⁻¹) v`. The
  scalars agree by `refinedLeviHalfModulus_reverse`, using the published
  `normalizedRefinedJacquet_mk` and `normalizedRefinedOppositeJacquet_mk`.
- `isGeneralizedEigencharacter_reverse`: if `ψ` is a generalized
  eigencharacter of the upper action `a ↦ T.normalizedRefinedJacquet C D ρ (m_D(a))`,
  then `ψ ∘ MaximalConeAssembly.precomp (reverseLabel C D)⁻¹`, that is
  `c ↦ ψ(c ∘ (reverseLabel C D)⁻¹)`, is a generalized eigencharacter of the
  opposite action `c ↦ T.normalizedRefinedOppositeJacquet C D' ρ (m'(c))`.
  The witness vector is the image under `toOpposite`, nonzero by
  `fromOpposite_toOpposite`, with the same power.

## Summation by parts

The main theorem reuses
`ParabolicConeUniqueness.sum_mul_nonpos_of_antitone t x hx ht htot` from
[`ParabolicConeUniquenessProof`](ParabolicConeUniquenessProof.md):
let `t, x : Fin m → ℝ`, with `x`
antitone. Suppose every prefix sum `∑_(k ≤ i) t k` is at most `0`, and
`∑_k t k = 0`. Then `∑_k t k * x k ≤ 0`.

The separate helper `sum_mul_nonpos_of_antitone_of_nonneg` proves the bound for antitone
nonnegative vectors `y` and nonpositive prefixes, by induction on `m`. It
splits off `y (last)` times the full sum, which is nonpositive, and applies
the induction hypothesis to `y k - y (last)` on the first `m` coordinates.

## Proof of the main theorem

Fix the data of the dual-opposite statement and its hypothesis `hdual`. The
theorem applies `h` to the same data. It remains to prove the core
hypothesis: for a refinement `D`, an open-kernel character
`ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ` that is a generalized
eigencharacter of the upper action, and a tuple `a` with
`T.normalizedAbs (a (e(j,i)))` monotone in `i` for every `j`, show
`‖ψ(a)‖ ≤ 1`.

1. **Transport.** By `isGeneralizedEigencharacter_reverse`,
   `ψ' = ψ ∘ precomp (reverseLabel C D)⁻¹` is a generalized eigencharacter of
   the opposite action of `D'`.
2. **Eigenfunctional.** The opposite normalized refined Jacquet module is
   admissible (`Parabolic.isAdmissible_normalizedRefinedOppositeJacquet`). It
   stays admissible after restriction along the topological isomorphism
   `flattenedLeviEquivContinuous` (`isAdmissible_comp_continuousMulEquiv`).
   Compact open subgroups are cofinal in the flattened Levi
   (`T.leviCompactOpen`), and flattened block scalars are central
   (`blockScalarLevi_mem_center`). Hence
   `DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter`
   ([`DualEigenfunctionalExistence`](../Exponents/DualEigenfunctionalExistence.md))
   gives a nonzero `φ` on `RefinedOppositeJacquetModule C D' S.ρ` with
   `φ(Jbar_(D')(m'(c)) x) = ψ'(c) φ(x)`.
3. **Real part.** Precomposition with a relabelling is continuous, so `ψ'`
   has open kernel. `T.exists_isRealPartOf` gives `s` with
   `‖ψ'(c)‖ = ∏_b |c_b|^(s_b)`, where `|·| = T.normalizedAbs`.
4. **Prefixes and totals.** `hdual` at `D'`, `ψ'`, `s`, `φ` gives
   `∑_(k ≤ i) s(e'(j,k)) ≤ 0` for all `j` and `i`. Since the central
   character `ω` is unitary, the published `sum_fibre_eq_zero_of_unitary`
   (module `MaximalConeLifting`) and `sum_filter_flattenOuter` give
   `∑_i s(e'(j,i)) = 0` for every `j`.
5. **Chamber bound.** `ψ(a) = ψ'(a ∘ reverseLabel C D)`, so

   ```text
   ‖ψ(a)‖ = ∏_b |a(reverseLabel b)|^(s_b)
          = exp( ∑_j ∑_i s(e'(j,i)) · log |a(e(j, i.rev))| ).
   ```

   For fixed `j`, `i ↦ log |a(e(j, i.rev))|` is antitone, because the
   absolute values are positive and monotone in the inner index of `D` and
   `Fin.rev` reverses order. Summation by parts with the prefixes and the
   zero total from step 4 bounds each inner sum by `0`. So the exponent is
   nonpositive and `‖ψ(a)‖ ≤ 1`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is a derived adapter, internal to the project. It implements the
direction "core implies consumer" of the section "Relation between the two
forms" in
[`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md),
which describes that relation without proving it. The implementation
conjugates by blockwise block-reversal matrices, not by the long Weyl
element of each factor. It obtains the chamber bound by summation by parts
rather than by reversing the vector `s`. No literature result is formalized
here beyond these elementary steps; the mathematical sources of the two
propositions are listed in the statement module.
