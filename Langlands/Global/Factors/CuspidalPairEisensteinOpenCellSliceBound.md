# Power bounds for the Levi Whittaker coefficient of a cuspidal-pair section

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellSliceBound`. The general
statements are in namespace `Langlands.Global.AdelicBlockScalarSections`, the statements for
the two-block shape of the cuspidal-pair Eisenstein series in
`Langlands.Global.CuspidalPairEisenstein.OpenCellBound`.

For a block shape `B` of `GL_n` and block realizations `S_i`, the normalized Levi slices of a
smooth compact-finite block section are finite combinations of products of realized
automorphic forms (`AdelicBlockScalarSections.coefficientValues`). If every `S_i` is cuspidal
and irreducible, each realized form is bounded by a constant times `|det g|^(β_i)` with an
exponent `β_i` depending only on `S_i`; the module turns this into one bound
`C ∏_i |det m_i|^(β_i)` for all normalized slices at all points of the standard maximal compact
subgroup, and deduces a bound for the Levi Whittaker coefficient
(`CuspidalPairEisenstein.leviWhittaker`) of the twisted section `φ_s = φ · H^s` of a
cuspidal-pair section `φ` (`CuspidalPairEisenstein.IsSection`) at `p k`, `p` in the parabolic and
`k` in the standard maximal compact subgroup. Here `|det|` is `absDet`, the idelic absolute value
of the determinant.

Compactness of the adele quotient (`[CompactSpace (AdeleQuotient F)]`, as in the statement) is
assumed exactly by the results about cuspidal realizations and sections:
`exists_blockPowerWeight_bound` (the power bound for cuspidal coefficients),
`blockRealizations_isCuspidal` and `blockRealizations_isIrreducible` (the inducing pair
`(T, (T')^∨)`, which uses the contragredient of `T'`), `exists_slice_bound` and
`norm_leviWhittaker_le` (which assume `IsSection T T' φ`). The generic uniform slice estimate
`exists_norm_normalizedSlice_le` does not assume it: it takes a coefficient power bound as input
and uses compactness of the standard maximal compact subgroup. The weights and the identities
`blockPowerWeight_nonneg`, `pairWeight_nonneg`, `pairWeight_leviOf_unipotent_mul` and
`twisted_levi_mul_eq` do not assume it either.

## Content

Namespace `AdelicBlockScalarSections`:

- `blockPowerWeight β m = ∏_i |det m_i|^(β_i)` on the adelic Levi `FullLevi F B`;
  `blockPowerWeight_nonneg`.
- **`exists_blockPowerWeight_bound`**: if every block size is nonzero and every `S_i` is
  cuspidal and irreducible, there are exponents `β_i` such that every `f ∈ coefficientValues F B S`
  satisfies `‖f m‖ ≤ C_f · blockPowerWeight β m` for some `C_f ≥ 0`.
- **`exists_norm_normalizedSlice_le`**: under such a bound, for every smooth compact-finite block
  section `f` there is `C ≥ 0` with
  `‖normalizedSlice F B f k m‖ ≤ C · blockPowerWeight β m` for all `k` in `standardCompact F n`
  and all `m`; here `normalizedSlice F B f k m = δ_P(m)^(-1/2) f(m k)`.

Namespace `CuspidalPairEisenstein.OpenCellBound`, for the upper parabolic `P` of block sizes
`(r + 1, t + 1)` and `N = r + t + 2`:

- `pairWeight r t β₁ β₂ m = |det m₁|^(β₁) |det m₂|^(β₂)` for `m = diag(m₁, m₂)`;
  `pairWeight_nonneg`, and `pairWeight_leviOf_unipotent_mul` (left multiplication by upper
  unitriangular blocks does not change it).
- `blockRealizations_isCuspidal`, `blockRealizations_isIrreducible`: the block realizations
  `(T, (T')^∨)` of a cuspidal pair are cuspidal and irreducible.
- **`exists_slice_bound`**: for a section `φ` with `IsSection T T' φ` there are `β₁`, `β₂` and
  `C ≥ 0` with `|δ_P(m)^(-1/2) φ(m k)| ≤ C |det m₁|^(β₁) |det m₂|^(β₂)` for every adelic Levi
  element `m` and every `k` in the standard maximal compact subgroup.
- `twisted_levi_mul_eq`: `φ_s(m k) = levFactor s m · δ_P(m)^(-1/2) φ(m k)`, where
  `Oneplace.levFactor s m = δ_P(m)^(1/2) H(m)^s` and `H(m)^s = exp((s/N) log δ_P(m))`.
- **`norm_leviWhittaker_le`**: if `ψ` is a standard additive character, `φ` is a section with
  `IsSection T T' φ` and the slices of `φ` satisfy the bound of `exists_slice_bound`, then for every `s`, every `p` in the adelic
  parabolic with Levi part `m` and every `k` in the standard maximal compact subgroup,
  `|W_M(φ_s)(p k)| ≤ |levFactor s m| · C |det m₁|^(β₁) |det m₂|^(β₂)`.

## Proofs

- `exists_blockPowerWeight_bound`: each `S_i` has a central character
  (`OperatorRealization.existsUnique_hasCentralCharacter`, from irreducibility), so
  `RankinSelbergGlobal.CuspCentralBound.exists_norm_evaluate_le_rpow` gives one exponent `β_i`
  for all vectors of `S_i`. The bound holds for a block coefficient `∏_i f_i(m_i)` with the
  product of the constants, and the set of functions satisfying a bound
  `‖f‖ ≤ C · blockPowerWeight β` for some `C` is closed under sums and scalar multiples
  (span induction).
- `exists_norm_normalizedSlice_le` follows the proof of
  `AdelicBlockScalarSections.exists_norm_le_normalizedSlice_of_normOne` (module
  `Langlands.Global.Factors.CuspidalPairInducedIntegrability`), with the power bound in place of
  the bound on norm-one elements. All slices lie in one finite-dimensional space
  `V ⊆ coefficientValues` (`exists_finiteDimensional_compactSlices`). With evaluation points
  for `V` (`EisensteinJet.exists_evaluationEquiv`), the coordinates of the slice at `k` in a
  basis `b_j` are linear combinations of values `f(x_i k)`, which are continuous in `k`
  (`continuous_smoothBlockSection`) and hence bounded on the compact group; summing
  `|coordinate_j| · ‖b_j‖` gives the bound.
- `exists_slice_bound`: the previous two results for the section `smoothSection hφ` of the
  block realizations `blockRealizations T T'` (module
  `Langlands.Global.Factors.CuspidalPairSchemeAutomorphy`), whose underlying function is `φ`;
  the product over the two blocks is `prod_blocks`.
- `norm_leviWhittaker_le`: the Levi Whittaker coefficient is an iterated Whittaker coefficient
  over the quotients `N_(r+1)(F) \ N_(r+1)(𝔸)` and `N_(t+1)(F) \ N_(t+1)(𝔸)` of total mass one, so
  it suffices to bound `|φ_s(diag(u₁, u₂) p k)|` for upper unitriangular `u₁`, `u₂`
  (`RankinSelbergGlobal.Unfolding.norm_whittaker_le`, twice; `|ψ| = 1`). Writing `p` as its
  unipotent part times its Levi part `m` (`Oneplace.parabolic_eq_unipotent_mul_levi`), the
  point is `n · (Q m) k` with `Q = diag(u₁, u₂)` and `n` in the unipotent radical, and `φ_s` is
  left invariant under the radical (`Oneplace.twisted_unipotent_mul`). By `twisted_levi_mul_eq`
  and the slice bound, `|φ_s((Q m) k)| ≤ |levFactor s (Q m)| C pairWeight(Q m)`, and both factors
  are unchanged by `Q` (`Oneplace.levFactor_unipotent_mul`, `pairWeight_leviOf_unipotent_mul`).

## Provenance

Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`), proof
of Theorem 5.1, p. 352: the local components of the Fourier coefficient are "dominated by the
corresponding intertwining integral". The bound here is the pointwise ingredient of a global
analogue of this domination, not Shahidi's local statement: for `g = n m k`,
`W_M(φ_s)(g) = δ_P(m)^(1/2 + s/N) · W_(φ_k)(m)` with `φ_k` the Levi slice at `k`, and the cusp
forms in the slice grow at most like a power of `|det|`
(`CuspCentralBound.exists_norm_evaluate_le_rpow`). The power bound and its uniformity in `k`
are internal to the formal proof; the uniformity through a finite-dimensional space of slices
follows the Library's proof of
`AdelicBlockScalarSections.exists_norm_le_normalizedSlice_of_normOne`.
