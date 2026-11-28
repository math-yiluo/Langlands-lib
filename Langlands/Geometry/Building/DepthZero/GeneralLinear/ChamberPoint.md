# Parahorics at chamber points of the diagonal apartment of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.ChamberPoint`.

## Chambers in general (namespace `Langlands.Geometry.Building.ParahoricBuildingData`)

For parahoric building data `P` of any group:

- `zeroFixer_facet_eq_nonnegativeRootSubgroup_singleton`: under the apartment axioms and
  Axiom 4.1.8 (2) (`HasZeroFixerGenerators`), for a point `x` of the apartment on no root
  hyperplane, `P.zeroFixer (facet x) = P.nonnegativeRootSubgroup {x}`. Indeed
  `P.zeroFixer (facet x) ≤ P.zeroFixer {x} = P.nonnegativeRootSubgroup {x}` (Axiom 4.1.8 (2)
  for the bounded set `{x}`); conversely an affine root with `ψ(x) ≥ 0` has `ψ(x) > 0`, hence is
  positive on the whole facet of `x` (the facet relation `AffineRootSystem.facetRel` keeps the
  signs), so `P.nonnegativeRootSubgroup {x} ≤ P.nonnegativeRootSubgroup (facet x)`, which lies in
  `P.zeroFixer (facet x)` (`ParahoricBuildingData.nonnegativeRootSubgroup_le_zeroFixer`).
- `pointwiseFixer_smul_image_inf_zeroSubgroup`: the elements of `G(F)^0` fixing the translate
  `g · Y` of a set of the reduced building are the `g`-conjugates of those fixing `Y`
  (`ParahoricBuildingData.normal_zeroSubgroup`).

## Permutation matrices (namespace `Langlands.Geometry.Building.GeneralLinearParahoric`)

- `permGL_inv`, `permPoint_inv`: the inverse of the permutation matrix of `σ` is that of `σ⁻¹`.
- `permGL_conj_diagGL`, `conj_permPoint_diagPoint`: `m_σ diag(d) m_σ⁻¹ = diag(d ∘ σ)`.
- `conj_permPoint_transvectionPoint`: `m_σ (1 + t E_{ab}) m_σ⁻¹ = 1 + t E_{σ⁻¹ a, σ⁻¹ b}`
  (`permGL_conj_transvectionGL`).
- `conj_permPoint_symm_apply`, `conj_mul_symm_apply`, `perm_apply_inv_self`: bookkeeping for
  inverse conjugations.

## The Iwahori subgroup

`I = generalLinearIwahoriPoints F N` consists of the points whose matrix is an invertible
matrix over `𝒪_F` with entries below the diagonal in the maximal ideal
(`mem_generalLinearIwahoriPoints`).

- `mem_maximalIdeal_iff_localFieldOrder_pos`: a nonzero integral `s` lies in the maximal ideal
  exactly when `ord s > 0` (`FML.mem_maximalIdeal_iff_ord_pos`).
- `diagPoint_mem_iwahori`: invertible diagonal matrices with entries of valuation one lie in `I`.
- `transvectionPoint_mem_iwahori`: `1 + s E_{ij}` lies in `I` when `s` is integral and, if
  `i > j`, in the maximal ideal.

## Coordinates of a chamber point

- `exists_floor_perm_of_forall_ne_intCast`: if no difference `y_k − y_l` (`k ≠ l`) is an
  integer, the fractional parts `fract(y_k)` are distinct; with `a_k = ⌊y_k⌋` and the inverse
  `π` of the permutation sorting `−fract(y_k)` increasingly (`Tuple.sort`,
  `Tuple.monotone_sort`), so that `π l < π k` exactly when `fract(y_k) < fract(y_l)`, one has
  for `n ∈ ℤ`: `n + y_k − y_l ≥ 0` exactly when `n ≥ a_l − a_k + [π l < π k]`.
- `exists_forall_sub_ne_intCast`: the coordinates `y_k = k / (N + 1)` have no integral
  difference.
- `exists_rootValue_eq_sub_of`: for apartment data of the diagonal torus every family of root
  values `z_k − z_l` is realized by a point (translate any point,
  `exists_eval_coordCharacter`, `rootValue_mk_vadd`).

## Iwahori point parahorics

With `P' = P.basedTransport σ f h` as in
`Langlands.Geometry.Building.DepthZero.GeneralLinear.PointParahoric`:

- `nonnegativeRootSubgroup_singleton_eq_of_chamber`: **if, for `k ≠ l` and `n ∈ ℤ`,
  `n + c_{kl}(x) ≥ 0` exactly when `n ≥ a_l − a_k + [π l < π k]`, then
  `P'.nonnegativeRootSubgroup {x} = (d m) I (d m)⁻¹` with `d = diag(ϖ^{−a_k})` and `m` the
  permutation matrix of `π`.** For `⊆` (`nonnegativeRootSubgroup_singleton_le`), `(d m)⁻¹`
  sends a diagonal matrix with unit entries to such a matrix, and a generator `1 + t E_{kl}`
  with `ord t + c_{kl}(x) ≥ 0` to `1 + s E_{π k, π l}` with `ord s = ord t + a_k − a_l ≥
  [π l < π k]`, which lies in `I`. For `⊇`, the preimage in `GL_N(𝒪_F)` of
  `(d m)⁻¹ P'.nonnegativeRootSubgroup {x} (d m)` contains the invertible diagonal matrices, the
  `1 + c E_{ij}` with `i < j`, `c ∈ 𝒪_F`, and those with `i > j`, `c` in the maximal ideal: the
  conjugate by `d m` is `1 + s E_{kl}` with `π k = i`, `π l = j` and
  `ord s = ord c + a_l − a_k`, so `ord s + c_{kl}(x) ≥ 0` by the hypothesis since
  `ord c ≥ [j < i]`. By `mem_of_iwahori` it contains every matrix of the Iwahori form.

This is the computation of the Iwahori subgroups of `GL_N` as the parahorics of the chambers of
the standard apartment (Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge
University Press, 2023, Definition 7.4.5, §15.1 and 15.1.33; literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`), carried out here through the generators of
Axiom 4.1.8 (2) rather than through lattice chains.
