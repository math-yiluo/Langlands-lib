# Injective swaps of adjacent blocks are surjective

Module: `Langlands.Representation.Archimedean.RealSwapSurjectiveProof`.

## Result

`Langlands.Archimedean.realSwapInjectiveIntertwinerSurjective :
RealSwapInjectiveIntertwinerSurjectiveStatement`.

The statement is in module `RealLinkedJacquetPairReduction`. Let `pre`, `post` be lists of real
blocks, `x`, `y` real blocks, and `n = realRank (pre ++ x :: y :: post)`. Let `T` be a linear
map from the `O(n)`-finite functions of the standard module of `pre ++ x :: y :: post` to those
of `pre ++ y :: x :: post`. If `T` is injective and is a `(𝔤, K)`-intertwiner
(`IsRealStandardIntertwiner`), then `T` is surjective.

## Provenance

This is one input of the reduction `RealLinkedJacquetFunctionalReductionStatement`, which is
internal to the proof of `RealLinkedLanglandsQuotientNotLargeStatement`. The idea is standard.
On `O(n)`, the two standard modules differ only
by a permutation of the positions, so they have isomorphic restrictions to `O(n)`. Their
`O(n)`-isotypic components are finite-dimensional, so an injective intertwiner between them is
onto. The module does not prove the isomorphism or decompose into `O(n)`-types. It builds an
injective `O(n)`-map in the opposite direction and compares dimensions of spaces of
`O(n)`-intertwiners from a fixed finite-dimensional representation. It makes no literature
claim beyond the theorem above.

The proof uses these Library results:

- `realStandardAdmissible` (module `RealStandardModuleAdmissible`): real standard modules are
  admissible (`IsAdmissibleGKModule`). So for every continuous matrix representation `τ` of
  `O(n)`, the space `gkIntertwiners ρ d τ` of `O(n)`-intertwiners from `τ` is
  finite-dimensional.
- `isRealGKModule_realStandardModule`: every vector is `O(n)`-finite, and its matrix
  coefficients against linear functionals are continuous.
- `KFiniteDual.subMatrix` and `KFiniteDual.continuous_subMatrix`: the matrices of a
  finite-dimensional subrepresentation in a chosen basis, and their continuity.
- `PrincipalSeriesExtension.extension`, `extension_mem_kFiniteFunctions`,
  `extension_unitary`, `rightTranslation_extension`: a function on `O(n)` with the
  equivariance of the principal series under the diagonal signs extends to an `O(n)`-finite
  vector of the principal series. The extension commutes with right translation by `O(n)`.
- `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`: a vector of the principal series
  that vanishes on `O(n)` is zero.

It also uses the Library modules `RealInductionStagesSlice` and
`RealInductionStagesFourier`:

- `realPositionCharacter_append_left/right` and `realInducedBlockAt_append_left/right`: the
  position characters and induction blocks of an appended list.
- `InductionStages.mem_realStandardModule_of_unitaryCompact`: a vector of the principal
  series of the position characters lies in the standard module if its block Fourier
  coefficients of weight `|k| < |m|` vanish on `O(n)`.

## Declarations

All declarations except the main theorem are in the namespace
`Langlands.Archimedean.RealSwapSurjective`.

### Injective intertwiners in both directions

Here `K` is a group with a topology (no compatibility between the two is assumed), and `ρ`,
`σ` are representations of `K` on complex vector spaces `V`, `W`.

- `postComp T hT d τ : gkIntertwiners ρ d τ →ₗ[ℂ] gkIntertwiners σ d τ`, `A ↦ T ∘ A`, for a
  `K`-intertwiner `T : V → W`. `postComp_apply`.
- `postComp_injective`: `postComp` is injective when `T` is.
- `surjective_of_injective` (**dimension count**): let `ρ` and `σ` be admissible. Suppose every
  vector of `W` is `K`-finite with continuous coefficients. Let `T : V → W` and `Φ : W → V`
  be injective `K`-intertwiners. Then `T` is surjective.

### Permutation matrices

- `permMat τ`: the permutation matrix with `(P_τ M)_{ij} = M_{τ(i), j}`. `permMat_mul`.
- `permMat_mul_eq`: `P_τ M = N P_τ` when `M_{τ(i), τ(l)} = N_{i, l}` for all `i`, `l`.
- `permMat_mem_unitaryGroup`, `permU τ` (`P_τ` as an element of `O(n)`), `permU_val`.
- `permU_mul_signDiagonal`: `P_τ diag(sgn a) = diag(sgn (a ∘ τ)) P_τ`.
- `permMat_mul_blockRotation`: `P_τ r_p(θ) = r_{p'}(θ) P_τ` when `τ` maps `p'` to `p` and
  `p' + 1` to `p + 1`. Here `r_p(θ) = blockRotation n p θ` is the rotation in positions
  `p, p + 1`.

### Pulling back along a permutation of the positions

- `continuous_toUnits`: the inclusion `O(n) → GL_n(ℝ)` is continuous.
- `pull τ f (κ) = f(P_τ κ)`, a linear map from functions on `GL_n(ℝ)` to functions on `O(n)`.
  `pull_apply`, `continuous_pull`.
- `pull_rightTranslation`: `pull τ (R(k) f) (κ) = pull τ f (κ k)` for `k ∈ O(n)`.
- `finiteDimensional_pull`: if `f` is `O(n)`-finite, the right translates of `pull τ f` span a
  finite-dimensional space.
- `principalSeriesCharacter_signUnit_perm`, `pull_signDiagonal`: suppose the position
  characters satisfy `χ_{ds'}(i) = χ_{ds}(τ i)` for all `i`. If `f` lies in the principal
  series of `χ_{ds'}`, then `pull τ f` has the sign equivariance of the principal series of
  `χ_{ds}`.

### The injection

Here `ds`, `ds'` are lists of real blocks of rank `n` and `τ` is a permutation of `Fin n`.

- `extPull ds τ f = extension (pull τ f)`, extended with the exponents of `ds`.
  `extPull_unitary`: it agrees with `pull τ f` on `O(n)`.
- `extPull_mem_kFinite_principalSeries`: suppose `χ_{ds'}(i) = χ_{ds}(τ i)` for all `i`. If
  `f` is an `O(n)`-finite vector of the standard module of `ds'`, then `extPull ds τ f` is an
  `O(n)`-finite vector of the principal series of `χ_{ds}`.
- `extPull_mem`: suppose also that for every induction block `d` of `ds` at position `p`,
  `ds'` has the induction block `d` at a position `p'` with `τ(p') = p` and
  `τ(p' + 1) = p + 1`. Then `extPull ds τ f` is an `O(n)`-finite function of the standard
  module of `ds`.
- `exists_perm_injection` (**the injection**): under the same hypotheses there is an
  injective linear map from the `O(n)`-finite functions of the standard module of `ds'` to
  those of `ds` that commutes with `O(n)`. It is `f ↦ extPull ds τ f`.

### Exchanging two adjacent blocks

Here `P = realRank pre`, `a = x.rank` and `b = y.rank`.

- `swapIdx P a b i`: `i` for `i < P`; `i + a` for `P ≤ i < P + b`; `i - b` for
  `P + b ≤ i < P + a + b`; `i` otherwise. `swapIdx_lt`, `swapIdx_swapIdx`.
- `swapPerm P a b n h`: the permutation `i ↦ swapIdx P a b i` of `Fin n`, with inverse
  `swapIdx P b a`. `swapPerm_val`.
- `realRank_singleton`, `realRank_swap`.
- `pc_seg1` to `pc_seg4` and `ib_seg1` to `ib_seg4`: the position characters and induction
  blocks of `pre ++ u :: v :: post` on the four segments `pre`, `u`, `v`, `post`.
- `swap_positionCharacter`: `swapPerm` carries the position characters of
  `pre ++ y :: x :: post` to those of `pre ++ x :: y :: post`.
- `swap_inducedBlock`: every induction block `d` of `pre ++ x :: y :: post` at position `p`
  is an induction block of `pre ++ y :: x :: post` at a position `p'` with `τ(p') = p` and
  `τ(p' + 1) = p + 1`, for `τ = swapPerm`.

### Main theorem

- `Langlands.Archimedean.realSwapInjectiveIntertwinerSurjective`.

## Proof notes

`surjective_of_injective`. Take `w ∈ W`. Let `S` be the span of the orbit of `w`
(`FiniteVectors.orbitSubrepresentation`). It is finite-dimensional because `w` is `K`-finite.
Let `τ = KFiniteDual.subMatrix S` be its matrices in the basis `b = Module.finBasis`. `τ` is
continuous by `KFiniteDual.continuous_subMatrix`. Admissibility makes
`gkIntertwiners ρ d τ` and `gkIntertwiners σ d τ` finite-dimensional. Composition with `T` and
with `Φ` are injective maps between them, so they have the same finite dimension, and
`postComp T` is bijective. The map `ι : ℂ^d → W`, `x ↦ b.equivFun.symm x`, is a
`K`-intertwiner by `KFiniteDual.equivFun_symm_coordRep`. Hence `ι = T ∘ A` for some
`K`-intertwiner `A`. With `x` the coordinates of `w`, we get `w = ι x = T (A x)`.

`extPull_mem`. Membership in the principal series and `O(n)`-finiteness come from
`extPull_mem_kFinite_principalSeries`. The Fourier conditions are needed only on `O(n)`,
by `mem_realStandardModule_of_unitaryCompact`. For `κ ∈ O(n)`,
`extPull ds τ f (r_p(θ) κ) = f(r_{p'}(θ) P_τ κ)` by `permMat_mul_blockRotation`. So the
block Fourier coefficient of `extPull ds τ f` at `p` and `κ` is that of `f` at `p'` and
`P_τ κ`. It vanishes because `f` lies in the standard module of `ds'`.

`exists_perm_injection`. Linearity follows from the linearity of `pull` and
`PrincipalSeriesExtension.extensionLinear`. The map commutes with `O(n)` by
`rightTranslation_extension` and `pull_rightTranslation`. If `extPull ds τ f = 0`, then
`pull τ f` vanishes on `O(n)`. Then `f(g) = pull τ f (P_τ⁻¹ g) = 0` for `g ∈ O(n)`, and
`f = 0` by `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`.

`swap_positionCharacter`, `swap_inducedBlock`. These are case analyses over the four segments
of positions, using the segment lemmas and `omega`.

`realSwapInjectiveIntertwinerSurjective`. Let `ds = pre ++ x :: y :: post` and
`ds' = pre ++ y :: x :: post`. Both have rank `n`. The permutation
`swapPerm (realRank pre) x.rank y.rank n` satisfies the hypotheses of `exists_perm_injection`
by `swap_positionCharacter` and `swap_inducedBlock`. This gives an injective `O(n)`-map `Φ`
from the `O(n)`-finite functions of the standard module of `ds'` to those of `ds`.
`surjective_of_injective` then applies to `T` and `Φ`. Admissibility comes from
`realStandardAdmissible`, and `K`-finiteness and continuity of coefficients come from
`isRealGKModule_realStandardModule`. `T` commutes with `O(n)` by
`IsRealStandardIntertwiner.map_realStandardRep`.
