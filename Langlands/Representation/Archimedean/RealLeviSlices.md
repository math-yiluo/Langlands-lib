# Class slices of the dual principal series along a block diagonal Levi subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviSlices`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It is
the first of three modules (`RealLeviSlices`, `RealLeviProducts`, `RealLeviDensity`) for the
density step of the single-shot Langlands-quotient argument. The module states no `Prop`-valued
statement of its own. Its results are used by `RealLeviProducts` and `RealLeviDensity`, which
prove `RealLeviDensityStatement`.

The module restricts functions on `GL_N(ℝ)` to one diagonal block `GL_{sz_i}(ℝ)` of a block
diagonal Levi subgroup. Such a restriction of the dual principal series of a concatenated list of
real blocks lies in the dual principal series of the twisted class list (`slice`). It intertwines
the actions of the block's `O(sz_i)` and Lie algebra. No literature statement is claimed and
nothing is cited; the provenance is internal ("derived"). Unprefixed names below are in the
namespace `Langlands.Archimedean.RealLeviSlices`.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`.
From the earlier module `RealLeviChartIntegralStatement` of this task (namespace `RealLeviChart`):
for sizes `sz : Fin c → ℕ`, `start sz i = sz_0 + ⋯ + sz_{i-1}`, and `pos sz i a` is the global
position `start sz i + a` (as `finSigmaFinEquiv ⟨i, a⟩`). From `RealLeviParabolicIntegrationStatement`:
`blockDiagHom sz` is the ring homomorphism `(A_j)_j ↦ diag(A_0, …, A_{c-1})` (Mathlib
`blockDiagonal'` reindexed by `finSigmaFinEquiv`) and `blockDiagGL sz` is the induced group
homomorphism `∏_j GL_{sz_j}(ℝ) → GL_N(ℝ)`, `N = ∑_j sz_j`.

For a list of real blocks `ds`, `realPositionCharacter ds p` is the Library's character at the
position `p`, `dualChar χ = χ⁻¹` (`PartialJacquet`), and `principalSeriesCharacter ℝ N χ a =
∏_p χ_p(a_p) |a_p|^{(N-1)/2 - p}`. From `RealLeviDuality`: `DualSpace N ds` is the space of
`O(N)`-finite functions of `principalSeries ℝ N (dualChar (realPositionCharacter ds))`.

## Twisted and concatenated lists

**Twists** (section `Twist`).

* `twistBlock s b`: the block `b` with its exponent increased by `s` (a character block keeps its
  parity; an induced block keeps its weight). `twist s ds` maps `twistBlock s` over `ds`.
* `rank_twistBlock`, `realRank_twist`: twisting preserves ranks.
* `realBlockExponent_twistBlock`: the exponent increases by `s`.
* `realPositionCharacter_twist`: for `p < realRank ds`,
  `realPositionCharacter (twist s ds) p x = realPositionCharacter ds p x · |x|^s`.
* `realInducedBlockAt_twist`: the induction block at `p` of the twisted list is the twist of the
  induction block at `p`, with the same weight (`characterOfParams d.weight (d.exponent + s)`).
* `realPositionCharacter_one`: every position character takes the value `1` at `1`.

**Concatenation** (section `Append`). `realRank_append`, and the position characters and
induction blocks of `A ++ B`: at `p < realRank A` they are those of `A`
(`realPositionCharacter_append_left`, `realInducedBlockAt_append_left`), and at
`realRank A + p` they are those of `B` at `p` (`..._append_right`).

**Lists of classes** (section `Flat`, `dss : Fin c → List RealBlock`).

* `flat dss = dss 0 ++ ⋯ ++ dss (c-1)` (`(List.ofFn dss).flatten`); `sz dss i = realRank (dss i)`;
  `flat_succ`.
* `realRank_flat`: `realRank (flat dss) = ∑_i sz dss i`.
* `start_zero'`, `start_succ'`: recursion for `start`.
* `realPositionCharacter_flat`, `realInducedBlockAt_flat`: at the global position
  `start (sz dss) i + a` with `a < sz dss i`, the position character and the induction block of
  `flat dss` are those of `dss i` at `a`.
* `shift dss i = start_i - (N - sz_i)/2` with `N = ∑_j sz dss j`, and
  `cl dss i = twist (shift dss i) (dss i)`, the **twisted class list**. `realRank_cl`:
  `realRank (cl dss i) = sz dss i`.

The twist is chosen so that the global character restricts to the class character. At the
global position `start_i + b` the global dual character has the exponent
`-e + (N-1)/2 - start_i - b` (where `e` is the exponent of `dss i` at `b`). The class dual
character of `cl dss i` at `b` has the exponent `-e - s_i + (sz_i - 1)/2 - b`. They agree exactly
when `s_i = start_i - (N - sz_i)/2`.

## Block embeddings

Section `Emb`, sizes `sz : Fin c → ℕ`, a class `i`.

* `embA sz i y = blockDiagHom sz (Pi.mulSingle i y)`: the matrix `diag(1, …, y, …, 1)`.
  `blockDiagLin sz` is `blockDiagHom sz` as a linear map, and
  `embL sz i Y = blockDiagHom sz (Pi.single i Y)` is the linear embedding
  `Y ↦ diag(0, …, Y, …, 0)` of `𝔤𝔩_{sz_i}(ℝ)`. `embA_eq`: `embA y = 1 + embL (y - 1)`.
  `embA_one`, `embA_mul`, `embA_eq_add` (affine form), `hasFDerivAt_embA` (derivative `embL`),
  `contDiff_embA`.
* `emb sz i : GL_{sz_i}(ℝ) →* GL_N(ℝ)`, `x ↦ blockDiagGL sz (Pi.mulSingle i x)` (`emb_eq`,
  `emb_val`: its matrix is `embA sz i x`).
* `emb_mem_unitaryCompact`, `emb_mem_upperUnipotent`: `emb` maps `O(sz_i)` into `O(N)` and upper
  unipotent matrices to upper unipotent matrices.
* `pad sz i a`: the global diagonal entries equal to `a` in the block `i` and `1` elsewhere.
  `emb_diagonalUnits`: `emb (diag(a)) = diag(pad a)`.
* `emb_mul_blockDiagGL_update`, `blockDiagGL_update_mul_emb`:
  `emb x · diag(g with 1 in block i) = diag(g with x in block i)`, and the same with the factors
  in the other order.
* `blockDiagGL_update_mul_embL`, `blockDiagGL_update_conj_embL`: `diag(g with 1 in block i)`
  commutes with `embL Y`.
* `embK sz i`: the restriction of `embA` to `O(sz_i) → O(N)` (Mathlib `unitaryGroup`), with
  `toUnits_embK`. `embLC sz i` is the complexification `ℂ ⊗ 𝔤𝔩_{sz_i}(ℝ) → ℂ ⊗ 𝔤𝔩_N(ℝ)` of `embL`
  (`LinearMap.baseChange`), with `embLC_tmul`.

## Smoothness and derivatives

Section `Smooth`, for `f` smooth on `GL_N(ℝ)` (`ContMDiff` for the Library's `matrixModel`).

* `contMDiff_comp_emb`: `x ↦ f(emb x)` is smooth on `GL_{sz_i}(ℝ)`. Proof: it is the restriction
  of the smooth map `y ↦ unitsExtension f (embA y)` on the open set of invertible matrices
  (Library `contDiffOn_unitsExtension`, `contMDiff_of_contDiffOn`).
* `rightDerivative_comp_emb`: the right derivative of `x ↦ f(emb x)` along `Y` at `x` is the
  right derivative of `f` along `embL Y` at `emb x`. Proof: by the Library
  `rightDerivative_eq_fderiv_mul_left` both sides are Fréchet derivatives at `1`. Near `1` the
  left side is `G ∘ embA` with `G(z) = unitsExtension f (emb x · z)`; then apply the chain rule
  with `hasFDerivAt_embA` and `embA_one`.

## Free algebras acting compatibly

Section `Free`, for complex vector spaces `V`, `W` and generators `g : ι → End V`,
`h : ι → End W`.

* `lift_intertwine`: if a linear map `T : V → W` satisfies `T (g x v) = h x (T v)`, then
  `T (lift g a v) = lift h a (T v)` for every `a` of the free algebra `FreeAlgebra ℂ ι`
  (induction on `a`).
* `lift_mem`: a submodule stable under every `g x` is stable under every `lift g a`.

## Slices of the dual space

Section `Slice`, for `dss : Fin c → List RealBlock` and a class `i`. Write `N = ∑_j sz dss j`,
`χ = realPositionCharacter (flat dss)` and `χ_i = realPositionCharacter (cl dss i)`.

* `pad_finSigmaFinEquiv`: evaluation of `pad` at a global position.
* `principalSeriesCharacter_pad`: `principalSeriesCharacter ℝ N (dualChar χ) (pad a) =
  principalSeriesCharacter ℝ sz_i (dualChar χ_i) a`. The product over the global positions is
  regrouped by classes (`finSigmaFinEquiv`, `Fintype.prod_sigma`). The classes `j ≠ i` contribute
  `1` (`realPositionCharacter_one`). The class `i` matches factor by factor by
  `realPositionCharacter_flat`, `realPositionCharacter_twist` and the choice of `shift`.
* `slice_mem`: for `u ∈ DualSpace N (flat dss)`, `x ↦ u(emb x)` lies in
  `DualSpace sz_i (cl dss i)`. It is smooth by `contMDiff_comp_emb`. It is equivariant because
  `emb (diag(a) n g) = diag(pad a) · emb n · emb g` with `emb n` upper unipotent, together with
  `principalSeriesCharacter_pad`. Its `O(sz_i)`-orbit span is contained in the image of the
  (finite-dimensional) `O(N)`-orbit span of `u` under composition with `emb`.
* `slice dss i : DualSpace N (flat dss) →ₗ[ℂ] DualSpace sz_i (cl dss i)`, `u ↦ u ∘ emb`, with
  `slice_apply`.
* Abbreviations: `repG dss`, `lieG dss` are the Library's `principalSeriesRep`,
  `principalSeriesLie` on the global dual space (character `dualChar χ`). `repC dss i`,
  `lieC dss i` are the same on the class dual space (character `dualChar χ_i`).
* `gensG dss i`: the free algebra generators of the class `i` acting on the global dual space,
  `GKModuleDensity.gens (repG dss) (lieG dss) ∘ Sum.map (embK i) (embLC i)`, so that `k ∈ O(sz_i)`
  acts by `repG (embK k)` and `X ∈ ℂ ⊗ 𝔤𝔩_{sz_i}(ℝ)` by `lieG (embLC X)` (`gensG_inl`,
  `gensG_inr`).
* `slice_rep`: `slice (repG (embK k) u) = repC k (slice u)`.
* `slice_lie`: `slice (lieG (embLC X) u) = lieC X (slice u)`. On pure tensors this is
  `rightDerivative_comp_emb`, using the Library formula `coe_principalSeriesLie_tmul`.
* `slice_gensG`, `slice_lift`: slicing intertwines `gensG dss i` with the class generators
  `GKModuleDensity.gens (repC dss i) (lieC dss i)`, hence the free algebra actions
  (`lift_intertwine`).
* `repG_comm_lieG`, `repG_comm_gensG`, `repG_comm_lift`: if `m ∈ O(N)` is
  `diag(g with 1 in block i)`, then `repG m` commutes with `gensG dss i x` and with every
  `lift (gensG dss i) a`. For the group generators this is `blockDiagGL_update_mul_emb` and
  `emb_mul_blockDiagGL_update`. For the Lie generators it is the Library
  `rightTranslation_rightDerivative` (right translation conjugates a right derivative by `Ad`)
  together with `blockDiagGL_update_conj_embL`.
